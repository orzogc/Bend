// Native C translation of main.bend: histogram-equalized
// escape-time render, 4096x4096, signed 8.8 fixed point, ITERS
// branchless iterations per pixel (z freezes at escape).
// Build: clang -O3 -DNDEBUG -ffp-contract=off par_mandelbrot.c -lm
#include <stdint.h>
#include <stdio.h>

#ifndef ITERS
#define ITERS 51
#endif
#ifndef WIDTH
#define WIDTH 4096
#endif

static uint32_t value_select(uint32_t t, uint32_t x, uint32_t y) {
  return t ? y : x;
}

// arithmetic shift right by 8 over two's-complement u32
static uint32_t word_asr8(uint32_t v) {
  return (v >> 8) | value_select(v >> 31, 0, 4278190080u);
}

// ITERS branchless escape-time iterations: z steps while esc == 0 and
// freezes after, it counts the pre-escape iterations
static uint32_t pixel_iterate(uint32_t n, uint32_t cr, uint32_t ci) {
  uint32_t zr = 0, zi = 0, esc = 0, it = 0;
  for (; n; n--) {
    uint32_t r2 = word_asr8(zr * zr);
    uint32_t i2 = word_asr8(zi * zi);
    uint32_t e2 = esc | (r2 + i2 > 1024);
    uint32_t nzr = r2 - i2 + cr;
    uint32_t nzi = word_asr8(2 * (zr * zi)) + ci;
    zr = value_select(e2, nzr, zr);
    zi = value_select(e2, nzi, zi);
    esc = e2;
    it = it + (e2 == 0);
  }
  return it;
}

// one pixel: viewport [-2, 1) x [-1.5, 1.5) over the WIDTH^2 grid
static uint32_t pixel_escape(uint32_t id) {
  uint32_t cr = (id & (WIDTH - 1)) * 768 / WIDTH - 512;
  uint32_t ci = (id / WIDTH) * 768 / WIDTH - 384;
  return pixel_iterate(ITERS, cr, ci);
}

// escape time -> one of 8 buckets, knob-stable
static uint32_t pixel_bucket(uint32_t it) {
  uint32_t bq = it * 8 / ITERS;
  return value_select(bq > 7, bq, 7);
}

int main(void) {
  uint32_t total = (uint32_t)WIDTH * WIDTH;
  uint32_t h[8] = {0};
  for (uint32_t i = 0; i < total; i++)
    h[pixel_bucket(pixel_escape(i))]++;
  uint32_t lut[8], c = 0;
  for (int k = 0; k < 8; k++)
    c += h[k], lut[k] = c;
  uint32_t cn = lut[7];
  for (int k = 0; k < 8; k++)
    lut[k] = lut[k] * 255 / cn;
  uint32_t mix = lut[0];
  for (int k = 1; k < 8; k++)
    mix = mix * 2654435761u + lut[k];
  uint32_t r = 0;
  for (uint32_t i = 0; i < total; i++) {
    uint32_t it = pixel_escape(i);
    uint32_t col = lut[pixel_bucket(it)];
    r += col * (i * 2654435761u + 1) + it;
  }
  printf("%u\n", mix * 2654435761u + r);
  return 0;
}
