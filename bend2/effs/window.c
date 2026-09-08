// Window
// ======
//! use ./sys.c

#define IO_WIND  5
#define WIN_ROWS 64

// WinEvent ::=
//   | WinEvent(kind, args)
typedef struct {
  u32 kind;
  u32 args[4];
} WinEvent;

#if BEND_METAL

#import <AppKit/AppKit.h>
#import <QuartzCore/QuartzCore.h>

#define WIN_STR_(x) #x
#define WIN_STR(x)  WIN_STR_(x)
#define WIN_DEF(m)  "#define " #m " " WIN_STR(m) "\n"

typedef struct {
  u64 root;
  u32 w;
  u32 h;
  u32 k;
} WinArgs;

@interface BendView : NSView <NSWindowDelegate> {
  @public
  WinEvent* evs;
  u32       len;
  u32       cap;
  u32       w;
  u32       h;
  u64       flags;
}
@end

@implementation BendView

- (void)dealloc {
  free(evs);
}

- (CALayer*)makeBackingLayer {
  return [CAMetalLayer layer];
}

- (BOOL)acceptsFirstResponder {
  return YES;
}

- (BOOL)isFlipped {
  return YES;
}

- (void)push:(WinEvent)ev {
  if (len == cap) {
    cap = cap > 0 ? cap * 2 : 64;
    evs = io_mem(realloc(evs, cap * sizeof(WinEvent)));
  }
  evs[len] = ev;
  len += 1;
}

- (void)key:(NSEvent*)ev down:(BOOL)down {
  NSString* s = [ev.charactersIgnoringModifiers lowercaseString];
  u32 code = s.length > 0 ? [s characterAtIndex:0] : 65536 + ev.keyCode;
  WinEvent e = { 0, { code, down } };
  [self push:e];
}

- (void)keyDown:(NSEvent*)ev {
  [self key:ev down:YES];
}

- (void)keyUp:(NSEvent*)ev {
  [self key:ev down:NO];
}

- (void)flagsChanged:(NSEvent*)ev {
  u64 now = ev.modifierFlags;
  WinEvent e = { 0, { 65536 + ev.keyCode, (now & ~flags) != 0 } };
  [self push:e];
  flags = now;
}

- (NSPoint)at:(NSEvent*)ev {
  NSPoint p = [self convertPointToBacking:
    [self convertPoint:ev.locationInWindow fromView:nil]];
  return NSMakePoint(fmax(0, fmin(floor(p.x), w - 1)),
    fmax(0, fmin(floor(p.y), h - 1)));
}

- (void)mouse:(NSEvent*)ev down:(BOOL)down {
  NSPoint p = [self at:ev];
  WinEvent e = { 1, { p.x, p.y, (u32)ev.buttonNumber, down } };
  [self push:e];
}

- (void)move:(NSEvent*)ev {
  NSPoint p = [self at:ev];
  WinEvent e = { 2, { p.x, p.y } };
  [self push:e];
}

- (void)mouseDown:(NSEvent*)ev {
  [self mouse:ev down:YES];
}

- (void)mouseUp:(NSEvent*)ev {
  [self mouse:ev down:NO];
}

- (void)rightMouseDown:(NSEvent*)ev {
  [self mouse:ev down:YES];
}

- (void)rightMouseUp:(NSEvent*)ev {
  [self mouse:ev down:NO];
}

- (void)otherMouseDown:(NSEvent*)ev {
  [self mouse:ev down:YES];
}

- (void)otherMouseUp:(NSEvent*)ev {
  [self mouse:ev down:NO];
}

- (void)mouseMoved:(NSEvent*)ev {
  [self move:ev];
}

- (void)mouseDragged:(NSEvent*)ev {
  [self move:ev];
}

- (void)rightMouseDragged:(NSEvent*)ev {
  [self move:ev];
}

- (void)otherMouseDragged:(NSEvent*)ev {
  [self move:ev];
}

- (BOOL)windowShouldClose:(NSWindow*)sender {
  WinEvent e = { 3 };
  [self push:e];
  return NO;
}

@end

static NSWindow*                   window_rows[WIN_ROWS];
static id<MTLDevice>               window_dev;
static id<MTLCommandQueue>         window_que;
static id<MTLBuffer>               window_buf;
static id<MTLComputePipelineState> window_pso;
static u64                         window_len;

static const char* window_msl =
  "#include <metal_stdlib>\n"
  "using namespace metal;\n"
  WIN_DEF(TAG_CTR)
  WIN_DEF(RFC_BIT)
  WIN_DEF(LOC_MASK)
  "struct Args { ulong root; uint w; uint h; uint k; };\n"
  "ulong node(device const ulong* mem, ulong t) {\n"
  "  return t & RFC_BIT ? mem[t & LOC_MASK] >> 24 : t & LOC_MASK;\n"
  "}\n"
  "kernel void window_dev(device const ulong* mem [[buffer(0)]],\n"
  "  constant Args& a [[buffer(1)]],\n"
  "  texture2d<float, access::write> out [[texture(0)]],\n"
  "  uint2 p [[thread_position_in_grid]]) {\n"
  "  ulong t = a.root;\n"
  "  for (uint i = a.k; ((t >> 56) & 0x7f) == TAG_CTR;) {\n"
  "    uint j = 0;\n"
  "    if (i > 0) {\n"
  "      i -= 1;\n"
  "      j = ((p.y >> i) & 1) * 2 + ((p.x >> i) & 1);\n"
  "    }\n"
  "    t = mem[node(mem, t) + j];\n"
  "  }\n"
  "  float4 c = unpack_unorm4x8_to_float(uint(t & LOC_MASK));\n"
  "  out.write(float4(c.zyx, 1.0), p);\n"
  "}\n";

static bool window_boot(void) {
  if (window_pso != nil) {
    return true;
  }
  if (NSScreen.screens.count == 0) {
    return false;
  }
  window_dev = gpu_buf != nil ? gpu_dev : MTLCreateSystemDefaultDevice();
  if (window_dev == nil) {
    return false;
  }
  window_que = gpu_buf != nil ? gpu_que : [window_dev newCommandQueue];
  NSError* err = nil;
  id<MTLLibrary> lib = [window_dev
    newLibraryWithSource:[NSString stringWithUTF8String:window_msl]
    options:nil error:&err];
  if (lib == nil) {
    err_fail(ERR_FAIL, err.localizedDescription.UTF8String);
  }
  window_pso = [window_dev newComputePipelineStateWithFunction:
    [lib newFunctionWithName:@"window_dev"] error:&err];
  if (window_pso == nil) {
    err_fail(ERR_FAIL, err.localizedDescription.UTF8String);
  }
  [NSApplication sharedApplication];
  NSApp.activationPolicy = NSApplicationActivationPolicyRegular;
  [NSApp finishLaunching];
  return true;
}

static void window_pump(void) {
  @autoreleasepool {
    for (;;) {
      NSEvent* ev = [NSApp nextEventMatchingMask:NSEventMaskAny
        untilDate:NSDate.distantPast inMode:NSDefaultRunLoopMode dequeue:YES];
      if (ev == nil) {
        break;
      }
      [NSApp sendEvent:ev];
    }
  }
}

static IoFall window_make(const char* title, u32 w, u32 h, int* row) {
  if (w < 1 || h < 1 || w > 16384 || h > 16384) {
    return io_sys_fall(EINVAL);
  }
  int i = 0;
  while (i < WIN_ROWS && window_rows[i] != nil) {
    i += 1;
  }
  if (i == WIN_ROWS) {
    return io_sys_fall(EMFILE);
  }
  if (!window_boot()) {
    IoFall q = { ENXIO, "Window.open: no display session" };
    return q;
  }
  @autoreleasepool {
    NSWindow* win = [[NSWindow alloc]
      initWithContentRect:NSMakeRect(0, 0, 1, 1)
      styleMask:NSWindowStyleMaskTitled | NSWindowStyleMaskClosable
        | NSWindowStyleMaskMiniaturizable
      backing:NSBackingStoreBuffered defer:NO];
    CGFloat scale = win.backingScaleFactor;
    win.releasedWhenClosed = NO;
    win.acceptsMouseMovedEvents = YES;
    win.title = [NSString stringWithCString:title
      encoding:NSISOLatin1StringEncoding];
    [win setContentSize:NSMakeSize(w / scale, h / scale)];
    BendView* view = [[BendView alloc] initWithFrame:win.contentLayoutRect];
    view->w = w;
    view->h = h;
    view->flags = NSEvent.modifierFlags;
    view.wantsLayer = YES;
    CAMetalLayer* layer = (CAMetalLayer*)view.layer;
    layer.device = window_dev;
    layer.pixelFormat = MTLPixelFormatBGRA8Unorm;
    layer.framebufferOnly = NO;
    layer.contentsScale = scale;
    layer.drawableSize = CGSizeMake(w, h);
    layer.displaySyncEnabled = YES;
    layer.maximumDrawableCount = 2;
    win.contentView = view;
    win.delegate = view;
    [win makeFirstResponder:view];
    [win center];
    [win makeKeyAndOrderFront:nil];
    [NSApp activateIgnoringOtherApps:YES];
    window_rows[i] = win;
  }
  *row = i;
  return io_sys_done();
}

static id<MTLBuffer> window_corpus(Env e) {
  if (gpu_buf != nil) {
    return gpu_buf;
  }
  u64 bump = a32_load(a32_at(e.mem, H_BUMP));
  u64 need = ((HEAP_OFF + (bump << PAGE_BITS)) * 8 + 16383) & ~16383ull;
  if (need > window_len) {
    u64 most = [window_dev maxBufferLength] & ~16383ull;
    if (need > most) {
      err_fail(ERR_HEAP, "the frame's memory is past the Metal buffer limit");
    }
    u64 len = window_len * 2 > need ? window_len * 2 : need;
    len = len < most ? len : most;
    window_buf = [window_dev newBufferWithBytesNoCopy:e.mem length:len
      options:MTLResourceStorageModeShared
        | MTLResourceHazardTrackingModeUntracked deallocator:nil];
    if (window_buf == nil) {
      err_fail(ERR_HEAP, "the corpus prefix does not map as a Metal buffer");
    }
    window_len = len;
  }
  return window_buf;
}

static void window_show(Env e, int row, Term image) {
  BendView* view = (BendView*)window_rows[row].contentView;
  id<MTLBuffer> buf = window_corpus(e);
  WinArgs args = { image, view->w, view->h, 0 };
  while ((1u << args.k) < args.w || (1u << args.k) < args.h) {
    args.k += 1;
  }
  window_pump();
  @autoreleasepool {
    id<CAMetalDrawable> d = [(CAMetalLayer*)view.layer nextDrawable];
    if (d == nil) {
      return;
    }
    id<MTLCommandBuffer> cb = [window_que commandBuffer];
    id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
    NSUInteger tw = window_pso.threadExecutionWidth;
    [enc setComputePipelineState:window_pso];
    [enc setBuffer:buf offset:0 atIndex:0];
    [enc setBytes:&args length:sizeof(args) atIndex:1];
    [enc setTexture:d.texture atIndex:0];
    [enc dispatchThreads:MTLSizeMake(args.w, args.h, 1)
      threadsPerThreadgroup:MTLSizeMake(tw,
        window_pso.maxTotalThreadsPerThreadgroup / tw, 1)];
    [enc endEncoding];
    [cb presentDrawable:d];
    [cb commit];
    [cb waitUntilCompleted];
    if (cb.error != nil) {
      err_fail(ERR_FAIL, cb.error.localizedDescription.UTF8String);
    }
  }
}

static Term window_node(Env e, WinEvent ev) {
  static const u32 cids[3] = { CID_KEY, CID_MOUSE, CID_MOVE };
  if (ev.kind == 3) {
    return term_pak(CID_CLOSE, 0);
  }
  u32 n = ev.kind == 1 ? 4 : 2;
  Loc l = heap_alloc(e, cls_fit(n));
  for (u32 j = 0; j < n; j += 1) {
    e.mem[l + j] = ev.args[j];
  }
  return term_ctr(cids[ev.kind], l);
}

static Term window_events(Env e, int row) {
  BendView* view = (BendView*)window_rows[row].contentView;
  Term list = term_pak(CID_NIL, 0);
  for (u32 i = view->len; i > 0;) {
    i -= 1;
    Loc l = heap_alloc(e, 1);
    e.mem[l]     = io_seal(e, window_node(e, view->evs[i]), IO_HOTS & 16);
    e.mem[l + 1] = io_seal(e, list, IO_HOTS & 16);
    list = term_ctr(CID_CON, l);
  }
  view->len = 0;
  return list;
}

static void window_drop(int row) {
  [window_rows[row] close];
  window_rows[row] = nil;
}

#else

static IoFall window_make(const char* title, u32 w, u32 h, int* row) {
  IoFall q = { ENOTSUP, "Window.open: this binary has no display kit" };
  return q;
}

static void window_show(Env e, int row, Term image) {
}

static Term window_events(Env e, int row) {
  return term_pak(CID_NIL, 0);
}

static void window_drop(int row) {
}

#endif
