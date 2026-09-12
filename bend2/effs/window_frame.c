// Window
// ======

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

static void window_pipe(id<MTLDevice> dev) {
  if (window_pso != nil) {
    return;
  }
  window_que = gpu_buf != nil ? gpu_que : [dev newCommandQueue];
  NSError* err = nil;
  id<MTLLibrary> lib = [dev
    newLibraryWithSource:[NSString stringWithUTF8String:window_msl]
    options:nil error:&err];
  if (lib == nil) {
    err_fail(err.localizedDescription.UTF8String);
  }
  window_pso = [dev newComputePipelineStateWithFunction:
    [lib newFunctionWithName:@"window_dev"] error:&err];
  if (window_pso == nil) {
    err_fail(err.localizedDescription.UTF8String);
  }
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

static id<MTLBuffer> window_corpus(Env e, id<MTLDevice> dev) {
  if (gpu_buf != nil) {
    return gpu_buf;
  }
  u64 bump = a32_load(a32_at(e.mem, H_BUMP));
  u64 need = ((HEAP_OFF + (bump << PAGE_BITS)) * 8 + 16383) & ~16383ull;
  if (need > window_len) {
    u64 most = [dev maxBufferLength] & ~16383ull;
    if (need > most) {
      err_fail("the frame's memory is past the Metal buffer limit");
    }
    u64 len = window_len * 2 > need ? window_len * 2 : need;
    len = len < most ? len : most;
    window_buf = [dev newBufferWithBytesNoCopy:e.mem length:len
      options:MTLResourceStorageModeShared
        | MTLResourceHazardTrackingModeUntracked deallocator:nil];
    if (window_buf == nil) {
      err_fail("the corpus prefix does not map as a Metal buffer");
    }
    window_len = len;
  }
  return window_buf;
}

static void window_show(Env e, CAMetalLayer* layer, Term image) {
  id<MTLDevice> dev = layer.device;
  window_pipe(dev);
  id<MTLBuffer> buf = window_corpus(e, dev);
  WinArgs args = { image, layer.drawableSize.width, layer.drawableSize.height,
    0 };
  while ((1u << args.k) < args.w || (1u << args.k) < args.h) {
    args.k += 1;
  }
  window_pump();
  @autoreleasepool {
    id<CAMetalDrawable> d = [layer nextDrawable];
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
      err_fail(cb.error.localizedDescription.UTF8String);
    }
  }
}

static Term window_node(Env e, const u32* ev) {
  static const u32 cids[3] = { CID_KEY, CID_MOUSE, CID_MOVE };
  if (ev[0] == 3) {
    return term_pak(CID_CLOSE, 0);
  }
  u32 n = ev[0] == 1 ? 4 : 2;
  Loc l = heap_alloc(e, cls_fit(n));
  for (u32 j = 0; j < n; j += 1) {
    e.mem[l + j] = ev[1 + j];
  }
  return term_ctr(cids[ev[0]], l);
}

static Term window_events(Env e, NSMutableData* evs) {
  const u32* p    = evs.bytes;
  Term       list = term_pak(CID_NIL, 0);
  for (u64 i = evs.length / 20; i > 0;) {
    i -= 1;
    Loc l = heap_alloc(e, 1);
    e.mem[l]     = io_seal(e, window_node(e, p + 5 * i), IO_HOTS & 16);
    e.mem[l + 1] = io_seal(e, list, IO_HOTS & 16);
    list = term_ctr(CID_CON, l);
  }
  evs.length = 0;
  return list;
}

static Term window_frame(Env e, intptr_t at, Term image) {
  NSView* view = ((__bridge NSWindow*)(void*)at).contentView;
  io_sync();
  window_show(e, (CAMetalLayer*)view.layer, image);
  return window_events(e, [view valueForKey:@"evs"]);
}

#else

static Term window_frame(Env e, intptr_t at, Term image) {
  return term_pak(CID_NIL, 0);
}

#endif

Term window_frame_run(Env e, Term* f, IoWork* w) {
  Term events = window_frame(e, (intptr_t)io_hand_v(f[0]), f[1]);
  return io_tup(e, f[0], io_tup(e, f[1], events));
}

static void __attribute__((constructor)) window_frame_use(void) {
  io_eff(CID_WINDOW_FRAME, window_frame_run, 0);
}
