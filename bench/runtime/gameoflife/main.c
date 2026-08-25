// Native C twin of main.bend: Conway soup census. Single-threaded,
// 1-to-1 with the Bend program: same bit-packed 4x4-torus step, SWAR
// popcount, two-probe classification, 64-soup chunk accumulators and census
// merge, same wrapping-u32 numerics.
#include <stdint.h>
#include <stdio.h>

typedef enum Cls {
  CLS_STILL,
  CLS_OSC,
  CLS_CHAOS,
} Cls;

typedef struct Census {
  uint32_t pop;
  uint32_t still;
  uint32_t osc;
  uint32_t mix;
} Census;

static uint32_t cell_get(uint32_t board, uint32_t r, uint32_t c) {
  return (board >> (((r & 3u) * 4u + (c & 3u)) & 31u)) & 1u;
}

static uint32_t neighbor_count(uint32_t board, uint32_t r, uint32_t c) {
  return cell_get(board, r - 1u, c - 1u) + cell_get(board, r - 1u, c) +
         cell_get(board, r - 1u, c + 1u) + cell_get(board, r, c - 1u) +
         cell_get(board, r, c + 1u) + cell_get(board, r + 1u, c - 1u) +
         cell_get(board, r + 1u, c) + cell_get(board, r + 1u, c + 1u);
}

static uint32_t to_bool(uint32_t k) { return k == 0u ? 0u : 1u; }

static uint32_t next_dead(uint32_t n) { return to_bool(n == 3u); }

static uint32_t next_alive(uint32_t n) {
  return to_bool((n == 2u) | (n == 3u));
}

static uint32_t next_cell(uint32_t a, uint32_t n) {
  return a == 0u ? next_dead(n) : next_alive(n);
}

static uint32_t step_cell(uint32_t board, uint32_t pos) {
  uint32_t r = pos >> 2u;
  uint32_t c = pos & 3u;
  uint32_t alive = cell_get(board, r, c);
  uint32_t neighbors = neighbor_count(board, r, c);
  return next_cell(alive, neighbors) << (pos & 31u);
}

static uint32_t board_step(uint32_t b) {
  uint32_t next = 0u;
  for (uint32_t pos = 0u; pos < 16u; ++pos) {
    next |= step_cell(b, pos);
  }
  return next;
}

static uint32_t board_run(uint32_t n, uint32_t board) {
  while (n != 0u) {
    board = board_step(board);
    --n;
  }
  return board;
}

// 16-bit SWAR population count
static uint32_t board_popcount(uint32_t b) {
  uint32_t a = b - ((b >> 1u) & 21845u);
  uint32_t c = (a & 13107u) + ((a >> 2u) & 13107u);
  uint32_t d = (c + (c >> 4u)) & 3855u;
  return (d * 257u >> 8u) & 31u;
}

// classify the settled board by two probe steps
static Cls board_classify(uint32_t b) {
  uint32_t n1 = board_step(b);
  if (n1 == b) {
    return CLS_STILL;
  }
  uint32_t n2 = board_step(n1);
  return n2 == b ? CLS_OSC : CLS_CHAOS;
}

// one soup: hash the soup index into a 16-bit board, run GENS steps
static uint32_t soup_sim(uint32_t ix, uint32_t g) {
  return board_run(g, (ix * 2654435761u) & 65535u);
}

// leaf chunk: 64 soups folded into scalar accumulators
static Census chunk_run(uint32_t j, uint32_t i, uint32_t g) {
  uint32_t pa = 0u;
  uint32_t sa = 0u;
  uint32_t oa = 0u;
  uint32_t mx = 0u;
  while (j != 0u) {
    uint32_t bd = soup_sim(i + j - 1u, g);
    uint32_t p = board_popcount(bd);
    Cls c = board_classify(bd);
    mx = (mx * 2654435761u) ^ bd;
    pa += p;
    sa += c == CLS_STILL ? 1u : 0u;
    oa += c == CLS_OSC ? 1u : 0u;
    --j;
  }
  return (Census){pa, sa, oa, mx};
}

static Census census_zip(Census a, Census b) {
  return (Census){a.pop + b.pop, a.still + b.still, a.osc + b.osc,
                  a.mix * 2654435761u + b.mix};
}

static Census batch_run(uint32_t d, uint32_t i, uint32_t g) {
  if (d == 0u) {
    return chunk_run(64u, i, g);
  }
  Census a = batch_run(d - 1u, i, g);
  Census b = batch_run(d - 1u, i + (64u << (d - 1u)), g);
  return census_zip(a, b);
}

// final checksum: mix the census fields
static uint32_t census_fin(Census c) {
  return ((c.pop * 2654435761u + c.still) * 2654435761u + c.osc) *
             2654435761u +
         c.mix;
}

int main(void) {
  uint32_t size = 18u;
  uint32_t gens = 32u;
  printf("%u\n", census_fin(batch_run(size, 0u, gens)));
  return 0;
}
