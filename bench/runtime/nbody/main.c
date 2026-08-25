// Native C translation of main.bend: chaotic three-body ensemble,
// f32, Plummer-softened, symplectic Euler; 2^(SY+3) seeded systems, ST
// steps each; checksum mixes the outcome histogram and digest sum.
// Build: clang -O3 -DNDEBUG -ffp-contract=off par_nbody.c -lm
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifndef SY
#define SY 17
#endif
#ifndef ST
#define ST 300
#endif

static uint32_t word_prng(uint32_t x) {
  uint32_t b = x ^ (x << 13), d = b ^ (b >> 17);
  return d ^ (d << 5);
}

// f32_to_u32: truncate toward zero; NaN, negative, or >= 2^32 -> 0
static uint32_t float_word(float f) {
  uint32_t b;
  memcpy(&b, &f, 4);
  if (b >> 31)
    return 0;
  uint32_t e = (b >> 23) & 0xff;
  if (e < 127 || e >= 159)
    return 0;
  uint32_t m = (b & 0x7fffff) | 0x800000;
  return e >= 150 ? m << (e - 150) : m >> (150 - e);
}

static float seed_unit(uint32_t sd, uint32_t k) {
  uint32_t h = word_prng((sd * 12 + k) * 2654435761u);
  return (float)(h & 65535) / 32768.0f - 1.0f;
}

static float seed_mass(uint32_t sd, uint32_t k) {
  uint32_t h = word_prng((sd * 12 + k) * 2654435761u);
  return (float)(h & 65535) / 65536.0f + 0.5f;
}

// one random system: three seeded bodies, ST steps, digest cs + energy
// bucket eb
static void system_run(uint32_t sd, uint32_t st, uint32_t *cs, uint32_t *eb) {
  float x0 = seed_unit(sd, 1), y0 = seed_unit(sd, 2), z0 = seed_unit(sd, 3);
  float m0 = seed_mass(sd, 4);
  float x1 = seed_unit(sd, 5), y1 = seed_unit(sd, 6), z1 = seed_unit(sd, 7);
  float m1 = seed_mass(sd, 8);
  float x2 = seed_unit(sd, 9), y2 = seed_unit(sd, 10), z2 = seed_unit(sd, 11);
  float m2 = seed_mass(sd, 12);
  float vx0 = y0 * 0.1f, vy0 = 0.0f - x0 * 0.1f, vz0 = 0.0f;
  float vx1 = y1 * 0.1f, vy1 = 0.0f - x1 * 0.1f, vz1 = 0.0f;
  float vx2 = y2 * 0.1f, vy2 = 0.0f - x2 * 0.1f, vz2 = 0.0f;
  for (uint32_t s = st; s; s--) {
    float ax = x1 - x0, ay = y1 - y0, az = z1 - z0;
    float da = (ax * ax + (ay * ay + az * az)) + 0.05f;
    float ia = 1.0f / sqrtf(da);
    float i3a = (ia * ia) * ia;
    float qax = ax * i3a, qay = ay * i3a, qaz = az * i3a;
    float bx = x2 - x0, by = y2 - y0, bz = z2 - z0;
    float db = (bx * bx + (by * by + bz * bz)) + 0.05f;
    float ib = 1.0f / sqrtf(db);
    float i3b = (ib * ib) * ib;
    float qbx = bx * i3b, qby = by * i3b, qbz = bz * i3b;
    float cx = x2 - x1, cy = y2 - y1, cz = z2 - z1;
    float dc = (cx * cx + (cy * cy + cz * cz)) + 0.05f;
    float ic = 1.0f / sqrtf(dc);
    float i3c = (ic * ic) * ic;
    float qcx = cx * i3c, qcy = cy * i3c, qcz = cz * i3c;
    vx0 = vx0 + (qax * m1 + qbx * m2) * 0.001f;
    vy0 = vy0 + (qay * m1 + qby * m2) * 0.001f;
    vz0 = vz0 + (qaz * m1 + qbz * m2) * 0.001f;
    vx1 = vx1 + (qcx * m2 - qax * m0) * 0.001f;
    vy1 = vy1 + (qcy * m2 - qay * m0) * 0.001f;
    vz1 = vz1 + (qcz * m2 - qaz * m0) * 0.001f;
    vx2 = vx2 - (qbx * m0 + qcx * m1) * 0.001f;
    vy2 = vy2 - (qby * m0 + qcy * m1) * 0.001f;
    vz2 = vz2 - (qbz * m0 + qcz * m1) * 0.001f;
    x0 = x0 + vx0 * 0.001f;
    y0 = y0 + vy0 * 0.001f;
    z0 = z0 + vz0 * 0.001f;
    x1 = x1 + vx1 * 0.001f;
    y1 = y1 + vy1 * 0.001f;
    z1 = z1 + vz1 * 0.001f;
    x2 = x2 + vx2 * 0.001f;
    y2 = y2 + vy2 * 0.001f;
    z2 = z2 + vz2 * 0.001f;
  }
  // digest: kinetic - softened potential, bucketed; position hash
  float s0 = vx0 * vx0 + (vy0 * vy0 + vz0 * vz0);
  float s1 = vx1 * vx1 + (vy1 * vy1 + vz1 * vz1);
  float s2 = vx2 * vx2 + (vy2 * vy2 + vz2 * vz2);
  float k0 = (0.5f * m0) * s0;
  float k1 = (0.5f * m1) * s1;
  float k2 = (0.5f * m2) * s2;
  float ke = k0 + (k1 + k2);
  float ax = x1 - x0, ay = y1 - y0, az = z1 - z0;
  float da = (ax * ax + (ay * ay + az * az)) + 0.05f;
  float bx = x2 - x0, by = y2 - y0, bz = z2 - z0;
  float db = (bx * bx + (by * by + bz * bz)) + 0.05f;
  float cx = x2 - x1, cy = y2 - y1, cz = z2 - z1;
  float dc = (cx * cx + (cy * cy + cz * cz)) + 0.05f;
  float pa = (m0 * m1) / sqrtf(da);
  float pb = (m0 * m2) / sqrtf(db);
  float pc = (m1 * m2) / sqrtf(dc);
  float pe = pa + (pb + pc);
  float e = ke - pe;
  uint32_t nb = float_word(0.0f - e);
  *eb = nb > 7 ? 7 : nb;
  uint32_t w0 = float_word((x0 + 8.0f) * 65536.0f) * 31 +
                float_word((y0 + 8.0f) * 65536.0f);
  uint32_t w1 = float_word((x1 + 8.0f) * 65536.0f) * 31 +
                float_word((y1 + 8.0f) * 65536.0f);
  uint32_t w2 = float_word((x2 + 8.0f) * 65536.0f) * 31 +
                float_word((y2 + 8.0f) * 65536.0f);
  uint32_t w3 = float_word((z0 + 8.0f) * 65536.0f) * 31 +
                float_word((z1 + 8.0f) * 65536.0f);
  uint32_t w4 = w0 * 2654435761u + w1;
  uint32_t w5 = w4 * 2654435761u + w2;
  uint32_t w6 = w5 * 2654435761u + w3;
  *cs = w6 * 2654435761u + float_word((z2 + 8.0f) * 65536.0f);
}

int main(void) {
  uint32_t count = 8u << SY;
  uint32_t h[8] = {0};
  uint32_t sum = 0;
  for (uint32_t sd = 0; sd < count; sd++) {
    uint32_t cs, eb;
    system_run(sd, ST, &cs, &eb);
    h[eb]++;
    sum += cs * (sd * 2654435761u + 1);
  }
  uint32_t g = h[0];
  for (int k = 1; k < 8; k++)
    g = g * 2654435761u + h[k];
  printf("%u\n", g * 2654435761u + sum);
  return 0;
}
