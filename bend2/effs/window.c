// Window
// ======
//! use ./sys.c
//$ -framework AppKit -framework QuartzCore

#ifndef __APPLE__
#error "Window: darwin only"
#endif

#include <objc/message.h>
#include <objc/objc.h>
#include <objc/runtime.h>
#include <ApplicationServices/ApplicationServices.h>
#include <time.h>

#define IO_WIND  5
#define WIN_ROWS 64
#define WIN_EVQ  256
#define WIN_TICK 16666667ULL

extern void* objc_autoreleasePoolPush(void);
extern void objc_autoreleasePoolPop(void* pool);

typedef id WinId;
typedef WinId (*WinMsg)(WinId, SEL);
typedef WinId (*WinMsgStr)(WinId, SEL, const char*);
typedef void (*WinMsgVoid)(WinId, SEL);
typedef void (*WinMsgId)(WinId, SEL, WinId);
typedef void (*WinMsgImg)(WinId, SEL, CGImageRef);
typedef void (*WinMsgLong)(WinId, SEL, long);
typedef void (*WinMsgBool)(WinId, SEL, BOOL);
typedef WinId (*WinMsgInit)(WinId, SEL, CGRect, unsigned long, unsigned long,
  BOOL);
typedef WinId (*WinMsgPoll)(WinId, SEL, unsigned long long, WinId, WinId,
  BOOL);
typedef long (*WinMsgGetLong)(WinId, SEL);
typedef unsigned long (*WinMsgGetULong)(WinId, SEL);
typedef unsigned short (*WinMsgGetUShort)(WinId, SEL);
typedef CGPoint (*WinMsgGetPoint)(WinId, SEL);

typedef struct {
  WinId     win;
  WinId     layer;
  uint32_t* fb[2];
  int       back;
  int       w;
  int       h;
  int       used;
  uint64_t  due;
  uint32_t  evq[WIN_EVQ];
  uint32_t  evq_h;
  uint32_t  evq_t;
} WinRow;

static WinRow window_rows[WIN_ROWS];
static WinId  window_delegate;

static const unsigned short window_keys[128] = {
  [0x00] = 'a',  [0x01] = 's',  [0x02] = 'd',  [0x03] = 'f',  [0x04] = 'h',
  [0x05] = 'g',  [0x06] = 'z',  [0x07] = 'x',  [0x08] = 'c',  [0x09] = 'v',
  [0x0B] = 'b',  [0x0C] = 'q',  [0x0D] = 'w',  [0x0E] = 'e',  [0x0F] = 'r',
  [0x10] = 'y',  [0x11] = 't',  [0x12] = '1',  [0x13] = '2',  [0x14] = '3',
  [0x15] = '4',  [0x16] = '6',  [0x17] = '5',  [0x18] = '=',  [0x19] = '9',
  [0x1A] = '7',  [0x1B] = '-',  [0x1C] = '8',  [0x1D] = '0',  [0x1E] = ']',
  [0x1F] = 'o',  [0x20] = 'u',  [0x21] = '[',  [0x22] = 'i',  [0x23] = 'p',
  [0x25] = 'l',  [0x26] = 'j',  [0x27] = '\'', [0x28] = 'k',  [0x29] = ';',
  [0x2A] = '\\', [0x2B] = ',',  [0x2C] = '/',  [0x2D] = 'n',  [0x2E] = 'm',
  [0x2F] = '.',  [0x32] = '`',
  [0x24] = 13,   [0x30] = 9,    [0x31] = ' ',  [0x33] = 8,    [0x35] = 27,
  [0x41] = '.',  [0x43] = '*',  [0x45] = '+',  [0x4B] = '/',  [0x4C] = 13,
  [0x4E] = '-',  [0x51] = '=',  [0x52] = '0',  [0x53] = '1',  [0x54] = '2',
  [0x55] = '3',  [0x56] = '4',  [0x57] = '5',  [0x58] = '6',  [0x59] = '7',
  [0x5B] = '8',  [0x5C] = '9',
  [0x75] = 127,  [0x7B] = 128,  [0x7C] = 129,  [0x7D] = 131,  [0x7E] = 130,
  [0x38] = 132,  [0x3C] = 132,  [0x3B] = 133,  [0x3E] = 133,  [0x3A] = 134,
  [0x3D] = 134,  [0x37] = 135,  [0x36] = 135,
};

static WinId window_str(const char* s) {
  return ((WinMsgStr)objc_msgSend)((WinId)objc_getClass("NSString"),
    sel_registerName("stringWithUTF8String:"), s);
}

static uint64_t window_now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static WinRow* window_at(WinId win) {
  for (int i = 0; i < WIN_ROWS; i += 1) {
    if (window_rows[i].used && window_rows[i].win == win) {
      return &window_rows[i];
    }
  }
  return NULL;
}

static void window_push(WinRow* row, uint32_t ev) {
  if (row->evq_t - row->evq_h < WIN_EVQ) {
    row->evq[row->evq_t & (WIN_EVQ - 1)] = ev;
    row->evq_t += 1;
  }
}

static BOOL window_should_close(WinId self, SEL cmd, WinId sender) {
  (void)self;
  (void)cmd;
  WinRow* row = window_at(sender);
  if (row != NULL) {
    window_push(row, 3u << 30);
  }
  return NO;
}

static long window_clamp(long v, int max) {
  if (v < 0) {
    return 0;
  }
  return v >= max ? max - 1 : v;
}

static uint32_t window_xy(WinRow* row, WinId ev, int* in) {
  CGPoint p = ((WinMsgGetPoint)objc_msgSend)(ev,
    sel_registerName("locationInWindow"));
  *in = p.x >= 0 && p.x < row->w && p.y >= 0 && p.y < row->h;
  long x = window_clamp((long)p.x, row->w);
  long y = window_clamp((long)(row->h - 1) - (long)p.y, row->h);
  return (uint32_t)x | ((uint32_t)y << 12);
}

static int window_event(WinId ev) {
  long ty = ((WinMsgGetLong)objc_msgSend)(ev, sel_registerName("type"));
  WinRow* row = window_at(((WinMsg)objc_msgSend)(ev,
    sel_registerName("window")));
  if (row == NULL) {
    return 0;
  }
  if (ty == 10 || ty == 11 || ty == 12) {
    uint32_t raw  = ((WinMsgGetUShort)objc_msgSend)(ev,
      sel_registerName("keyCode"));
    uint32_t code = raw < 128 && window_keys[raw] != 0
      ? window_keys[raw] : 0x1000 | raw;
    uint32_t down = ty == 10;
    if (ty == 12) {
      unsigned long flags = ((WinMsgGetULong)objc_msgSend)(ev,
        sel_registerName("modifierFlags"));
      down = code >= 132 && code <= 135 ? (flags >> (code - 115)) & 1 : 1;
    }
    window_push(row, down << 16 | code);
    return ty != 12;
  }
  int in;
  uint32_t xy = window_xy(row, ev, &in);
  if (ty == 1 || ty == 2 || ty == 3 || ty == 4 || ty == 25 || ty == 26) {
    uint32_t btn  = (uint32_t)((WinMsgGetLong)objc_msgSend)(ev,
      sel_registerName("buttonNumber"));
    uint32_t down = ty == 1 || ty == 3 || ty == 25;
    if (in) {
      window_push(row, 1u << 30 | down << 28 | (btn & 15) << 24 | xy);
    }
  } else if (ty == 5 || ty == 6 || ty == 7 || ty == 27) {
    if (in || ty != 5) {
      window_push(row, 2u << 30 | xy);
    }
  }
  return 0;
}

static void window_pump(void) {
  void* pool = objc_autoreleasePoolPush();
  WinId app  = ((WinMsg)objc_msgSend)((WinId)objc_getClass("NSApplication"),
    sel_registerName("sharedApplication"));
  WinId past = ((WinMsg)objc_msgSend)((WinId)objc_getClass("NSDate"),
    sel_registerName("distantPast"));
  WinId mode = window_str("kCFRunLoopDefaultMode");
  for (;;) {
    WinId ev = ((WinMsgPoll)objc_msgSend)(app,
      sel_registerName("nextEventMatchingMask:untilDate:inMode:dequeue:"),
      ~0ULL, past, mode, YES);
    if (ev == NULL) {
      break;
    }
    if (window_event(ev) == 0) {
      ((WinMsgId)objc_msgSend)(app, sel_registerName("sendEvent:"), ev);
    }
  }
  objc_autoreleasePoolPop(pool);
}

static void window_fill(WinRow* row, int x0, int y0, int sz, uint32_t c) {
  uint32_t* fb = row->fb[row->back];
  int x1 = x0 + sz < row->w ? x0 + sz : row->w;
  int y1 = y0 + sz < row->h ? y0 + sz : row->h;
  for (int y = y0; y < y1; y += 1) {
    uint32_t* line = fb + (size_t)y * (size_t)row->w;
    for (int x = x0; x < x1; x += 1) {
      line[x] = c;
    }
  }
}

static uint32_t window_pix(Env e, Term t) {
  while (term_tag(t) == TAG_CTR) {
    Term fb[4];
    spare_free(e, cls_fit(4), ctr_take(e, t, 4, fb));
    term_drop(e, fb[1]);
    term_drop(e, fb[2]);
    term_drop(e, fb[3]);
    t = fb[0];
  }
  return (uint32_t)term_loc(t);
}

static void window_walk(Env e, WinRow* row, Term t, int x0, int y0, int sz) {
  if (x0 >= row->w || y0 >= row->h) {
    term_drop(e, t);
    return;
  }
  if (term_tag(t) == TAG_CTR && sz > 1) {
    Term fb[4];
    spare_free(e, cls_fit(4), ctr_take(e, t, 4, fb));
    int hf = sz >> 1;
    window_walk(e, row, fb[0], x0, y0, hf);
    window_walk(e, row, fb[1], x0 + hf, y0, hf);
    window_walk(e, row, fb[2], x0, y0 + hf, hf);
    window_walk(e, row, fb[3], x0 + hf, y0 + hf, hf);
    return;
  }
  window_fill(row, x0, y0, sz, window_pix(e, t));
}

static void window_present(WinRow* row) {
  static CGColorSpaceRef cs;
  if (cs == NULL) {
    cs = CGColorSpaceCreateDeviceRGB();
  }
  CGContextRef cg = CGBitmapContextCreate(row->fb[row->back], (size_t)row->w,
    (size_t)row->h, 8, (size_t)row->w * 4, cs,
    kCGImageAlphaNoneSkipFirst | kCGBitmapByteOrder32Little);
  CGImageRef img = CGBitmapContextCreateImage(cg);
  ((WinMsgImg)objc_msgSend)(row->layer, sel_registerName("setContents:"), img);
  CGImageRelease(img);
  CGContextRelease(cg);
  row->back ^= 1;
}

static void window_pace(WinRow* row) {
  uint64_t now = window_now();
  uint64_t due = row->due + WIN_TICK;
  if (due + WIN_TICK < now) {
    due = now;
  }
  if (due > now) {
    struct timespec ts = { (time_t)((due - now) / 1000000000ULL),
      (long)((due - now) % 1000000000ULL) };
    nanosleep(&ts, NULL);
  }
  row->due = due;
}

static void window_drop(WinRow* row) {
  ((WinMsgVoid)objc_msgSend)(row->win, sel_registerName("close"));
  row->win   = NULL;
  row->layer = NULL;
  free(row->fb[0]);
  free(row->fb[1]);
  row->used = 0;
}
