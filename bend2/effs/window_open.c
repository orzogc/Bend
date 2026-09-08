// Window
// ======

#define IO_WIND 5

#if BEND_METAL

#import <AppKit/AppKit.h>
#import <QuartzCore/QuartzCore.h>

@interface BendView : NSView <NSWindowDelegate> {
  @public
  NSMutableData* evs;
  u64            flags;
}
@end

@implementation BendView

- (CALayer*)makeBackingLayer {
  return [CAMetalLayer layer];
}

- (BOOL)acceptsFirstResponder {
  return YES;
}

- (BOOL)isFlipped {
  return YES;
}

- (void)push:(u32)kind a:(u32)a b:(u32)b c:(u32)c d:(u32)d {
  u32 ev[5] = { kind, a, b, c, d };
  [evs appendBytes:ev length:sizeof ev];
}

- (void)key:(NSEvent*)ev down:(BOOL)down {
  NSString* s = [ev.charactersIgnoringModifiers lowercaseString];
  u32 code = s.length > 0 ? [s characterAtIndex:0] : 65536 + ev.keyCode;
  [self push:0 a:code b:down c:0 d:0];
}

- (void)keyDown:(NSEvent*)ev {
  [self key:ev down:YES];
}

- (void)keyUp:(NSEvent*)ev {
  [self key:ev down:NO];
}

- (void)flagsChanged:(NSEvent*)ev {
  u64 now = ev.modifierFlags;
  [self push:0 a:65536 + ev.keyCode b:(now & ~flags) != 0 c:0 d:0];
  flags = now;
}

- (NSPoint)at:(NSEvent*)ev {
  CGSize  size = ((CAMetalLayer*)self.layer).drawableSize;
  NSPoint p    = [self convertPointToBacking:
    [self convertPoint:ev.locationInWindow fromView:nil]];
  return NSMakePoint(fmax(0, fmin(floor(p.x), size.width - 1)),
    fmax(0, fmin(floor(p.y), size.height - 1)));
}

- (void)mouse:(NSEvent*)ev down:(BOOL)down {
  NSPoint p = [self at:ev];
  [self push:1 a:p.x b:p.y c:(u32)ev.buttonNumber d:down];
}

- (void)move:(NSEvent*)ev {
  NSPoint p = [self at:ev];
  [self push:2 a:p.x b:p.y c:0 d:0];
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
  [self push:3 a:0 b:0 c:0 d:0];
  return NO;
}

@end

static id<MTLDevice> window_dev;

static IoFall window_make(const char* title, u32 w, u32 h, IoHand* out) {
  if (w < 1 || h < 1 || w > 16384 || h > 16384) {
    return io_sys_fall(EINVAL);
  }
  if (NSScreen.screens.count == 0) {
    IoFall q = { ENXIO, "Window.open: no display session" };
    return q;
  }
  if (window_dev == nil) {
    window_dev = gpu_buf != nil ? gpu_dev : MTLCreateSystemDefaultDevice();
  }
  if (window_dev == nil) {
    IoFall q = { ENXIO, "Window.open: no Metal device" };
    return q;
  }
  if (NSApp == nil) {
    [NSApplication sharedApplication];
    NSApp.activationPolicy = NSApplicationActivationPolicyRegular;
    [NSApp finishLaunching];
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
    view->evs   = [NSMutableData new];
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
    if (io_sys_mint(IO_WIND, (intptr_t)(__bridge void*)win, out) < 0) {
      [win close];
      return io_sys_fall(EMFILE);
    }
    (void)CFBridgingRetain(win);
  }
  return io_sys_fall(0);
}

#else

static IoFall window_make(const char* title, u32 w, u32 h, IoHand* out) {
  IoFall q = { ENOTSUP, "Window.open: this binary has no display kit" };
  return q;
}

#endif

Term window_open_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* title = io_cstr(e, f[0], &n);
  IoHand out;
  IoFall q = io_nul(title, n) ? io_sys_fall(EILSEQ)
    : window_make(title, (u32)f[1], (u32)f[2], &out);
  free(title);
  if (q.code != 0) {
    return io_fail(e, q);
  }
  return io_done(e, io_hand(e, CID_WINDOW, out));
}

static void __attribute__((constructor)) window_open_use(void) {
  io_eff(FID_WINDOW_OPEN, CID_WINDOW_OPEN, window_open_run, 0);
}
