// par_queens: single-threaded C twin of main.bend, one C function per
// Bend def. batch forks the flat (c0,c1,c2,c3) prefix index space
// 0..2^DEPTH as a balanced tree; each leaf permutes its index by an odd
// multiplier, decodes its column quad (base-N digits) through the
// staged pfx_s1/s2/s3 legality checks, and solve runs the classic
// bitmask backtracker over the remaining N-4 rows: peel b = cand &
// -cand, descend on the child candidate word, tail-call on the sibling
// set. smerge adds Stats pairwise up the fork tree. As in the Bend
// defs, every decision bool is computed by the caller (z = cand == 0
// and e = nc == full arrive as arguments), a Nat fuel (u64, dead 0
// arm included) bounds the call depth, and the child's Stats result
// rides into the sibling call as the ret argument. Stats keeps both
// constructors (STAT0/STATS) as a tagged record returned by value: no
// heap. The sibling self-calls carry musttail: with 14 parameters the
// AArch64 backend refuses sibling-call TCO on its own, so without it
// every peel pushes a frame instead of looping.
// Checksum = (sols * 2654435761) ^ nodes.
// Expected at DEPTH=17, SIZE=17, LIMIT=11730: 2063750025.

#include <stdint.h>
#include <stdio.h>

#define DEPTH 17u
#define SIZE 17u
#define LIMIT 11730u
#define MUSTTAIL __attribute__((musttail))

enum { STAT0, STATS };
typedef struct {
  uint32_t tag, sols, nodes;
} Stats;

static uint32_t b2u(uint32_t b) { return b ? 1u : 0u; }

static uint32_t sel_go(uint32_t x, uint32_t y, uint32_t z) {
  return z ? x : y;
}

static uint32_t sel(uint32_t t, uint32_t x, uint32_t y) {
  return sel_go(x, y, t == 0u);
}

static uint32_t sq(uint32_t x) { return x * x; }

static Stats solve(uint64_t f, uint32_t z, uint32_t e, uint32_t sib,
                   uint32_t nc, uint32_t nl, uint32_t nr, uint32_t cols,
                   uint32_t ld, uint32_t rd, uint32_t full, Stats ret,
                   uint32_t sols, uint32_t nodes) {
  if (f == 0u) {
    if (ret.tag == STAT0)
      return (Stats){STATS, sols, nodes};
    return (Stats){STATS, sols + ret.sols, nodes + ret.nodes};
  }
  uint64_t g = f - 1u;
  if (z) {
    if (ret.tag == STAT0)
      return (Stats){STATS, sols, nodes};
    return (Stats){STATS, sols + ret.sols, nodes + ret.nodes};
  }
  if (e) {
    uint32_t c2 = sib;
    uint32_t b2 = c2 & (0u - c2);
    uint32_t n2 = cols | b2;
    if (ret.tag == STAT0)
      MUSTTAIL return solve(g, c2 == 0u, n2 == full, c2 - b2, n2,
                            (ld | b2) << 1, (rd | b2) >> 1, cols, ld, rd, full,
                            (Stats){STAT0, 0u, 0u}, sols + 1u, nodes + 1u);
    MUSTTAIL return solve(g, c2 == 0u, n2 == full, c2 - b2, n2, (ld | b2) << 1,
                          (rd | b2) >> 1, cols, ld, rd, full,
                          (Stats){STAT0, 0u, 0u}, sols + ret.sols + 1u,
                          nodes + ret.nodes + 1u);
  }
  uint32_t cc = full & ~(nc | (nl | nr));
  uint32_t cb = cc & (0u - cc);
  uint32_t cn = nc | cb;
  uint32_t c2 = sib;
  uint32_t b2 = c2 & (0u - c2);
  uint32_t n2 = cols | b2;
  if (ret.tag == STAT0)
    MUSTTAIL return solve(g, c2 == 0u, n2 == full, c2 - b2, n2, (ld | b2) << 1,
                          (rd | b2) >> 1, cols, ld, rd, full,
                          solve(g, cc == 0u, cn == full, cc - cb, cn,
                                (nl | cb) << 1, (nr | cb) >> 1, nc, nl, nr,
                                full, (Stats){STAT0, 0u, 0u}, sols,
                                nodes + 1u),
                          0u, 0u);
  MUSTTAIL return solve(g, c2 == 0u, n2 == full, c2 - b2, n2, (ld | b2) << 1,
                        (rd | b2) >> 1, cols, ld, rd, full,
                        solve(g, cc == 0u, cn == full, cc - cb, cn,
                              (nl | cb) << 1, (nr | cb) >> 1, nc, nl, nr, full,
                              (Stats){STAT0, 0u, 0u}, sols + ret.sols,
                              nodes + ret.nodes + 1u),
                        0u, 0u);
}

// one 4-row prefix: permute the fork index, decode the column quad,
// filter illegal placements, solve the remaining rows; each stage
// matches the bool its caller computed
static Stats pfx_s3(uint32_t t, uint32_t nn2, uint32_t full, uint32_t b3,
                    uint32_t c3, uint32_t l3, uint32_t r3) {
  if (!t)
    return (Stats){STATS, 0u, 0u};
  uint32_t c4 = c3 | b3;
  uint32_t l4 = (l3 | b3) << 1;
  uint32_t r4 = (r3 | b3) >> 1;
  uint32_t cc = full & ~(c4 | (l4 | r4));
  uint32_t cb = cc & (0u - cc);
  uint32_t cn = c4 | cb;
  return solve((uint64_t)nn2, cc == 0u, cn == full, cc - cb, cn,
               (l4 | cb) << 1, (r4 | cb) >> 1, c4, l4, r4, full,
               (Stats){STAT0, 0u, 0u}, 0u, 0u);
}

static Stats pfx_s2(uint32_t t, uint32_t nn2, uint32_t i, uint32_t nn,
                    uint32_t full, uint32_t b2, uint32_t c2, uint32_t l2,
                    uint32_t r2) {
  if (!t)
    return (Stats){STATS, 0u, 0u};
  uint32_t b3 = 1u << (i % nn);
  uint32_t c3 = c2 | b2;
  uint32_t l3 = (l2 | b2) << 1;
  uint32_t r3 = (r2 | b2) >> 1;
  return pfx_s3((b3 & (c3 | (l3 | r3))) == 0u, nn2, full, b3, c3, l3, r3);
}

static Stats pfx_s1(uint32_t t, uint32_t nn2, uint32_t i, uint32_t nn,
                    uint32_t full, uint32_t b0, uint32_t b1) {
  if (!t)
    return (Stats){STATS, 0u, 0u};
  uint32_t b2 = 1u << ((i / nn) % nn);
  uint32_t c2 = b0 | b1;
  uint32_t l2 = ((b0 << 1) | b1) << 1;
  uint32_t r2 = ((b0 >> 1) | b1) >> 1;
  return pfx_s2((b2 & (c2 | (l2 | r2))) == 0u, nn2, i, nn, full, b2, c2, l2,
                r2);
}

static Stats pfx_d(uint32_t nn2, uint32_t i, uint32_t nn, uint32_t full) {
  uint32_t b0 = 1u << (i / (nn2 * nn));
  uint32_t b1 = 1u << ((i / nn2) % nn);
  return pfx_s1((b1 & (b0 | ((b0 << 1) | (b0 >> 1)))) == 0u, nn2, i, nn, full,
                b0, b1);
}

static Stats pfx_go2(uint32_t t, uint32_t i, uint32_t nn, uint32_t full) {
  if (!t)
    return (Stats){STATS, 0u, 0u};
  return pfx_d(nn * nn, i, nn, full);
}

static Stats pfx_go(uint32_t i, uint32_t nn, uint32_t full, uint32_t bound) {
  return pfx_go2(i < bound, i, nn, full);
}

static Stats pfx(uint32_t j, uint32_t m, uint32_t nn, uint32_t full,
                 uint32_t bound) {
  return pfx_go((j * 2654435761u) & m, nn, full, bound);
}

static Stats smerge(Stats a, Stats b) {
  if (a.tag == STATS && b.tag == STATS)
    return (Stats){STATS, a.sols + b.sols, a.nodes + b.nodes};
  if (a.tag == STATS)
    return a;
  if (b.tag == STATS)
    return b;
  return (Stats){STAT0, 0u, 0u};
}

static Stats batch(uint64_t d, uint32_t i, uint32_t m, uint32_t nn,
                   uint32_t full, uint32_t bound) {
  if (d == 0u)
    return pfx(i, m, nn, full, bound);
  uint64_t p = d - 1u;
  Stats a = batch(p, i, m, nn, full, bound);
  Stats b = batch(p, i + (1u << p), m, nn, full, bound);
  return smerge(a, b);
}

static uint32_t run_fin(Stats st) {
  if (st.tag == STAT0)
    return 0u;
  return (st.sols * 2654435761u) ^ st.nodes;
}

static uint32_t run(uint64_t d, uint32_t n, uint32_t lim) {
  uint32_t nnnn = sq(sq(n));
  uint32_t full = (1u << n) - 1u;
  // bound = min-like clamp: lim when lim < n^4, else n^4
  return run_fin(batch(d, 0u, (1u << d) - 1u, n, full,
                       sel(b2u(lim < nnnn), nnnn, lim)));
}

static uint32_t size(void) { return SIZE; }

static uint32_t limit(void) { return LIMIT; }

int main(void) {
  printf("%u\n", run(DEPTH, size(), limit()));
  return 0;
}
