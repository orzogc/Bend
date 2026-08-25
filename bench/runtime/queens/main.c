// par_queens: single-threaded C twin of main.bend. Same
// algorithm, same shape: rows 0-3 are placed by walking the flat
// (c0,c1,c2,c3) prefix index space 0..2^17 (base-N digit decode + the
// solver's own bitmask legality rules), then board_solve runs the
// classic bitmask backtracker over the remaining N-4 rows, threading
// per-branch Stats{sols, nodes}. The Stats pairs are summed over the
// prefix space (the Bend fork tree's smerge reduction, associative).
// Same recursive backtracker as the Bend bench. Stats is a 2-word
// record returned by value: no heap.
// Checksum = (sols * 2654435761) ^ nodes.
// Build: clang -O3 -DNDEBUG -ffp-contract=off par_queens.c -lm
// Expected at SIZE=17, LIMIT=11730: 2063750025 (SIZE=8, LIMIT=512:
// 2027808349).

#include <stdint.h>
#include <stdio.h>

#define SIZE 17u
#define LIMIT 11730u
#define DEPTH 17u

typedef struct {
  uint32_t sols, nodes;
} Stats;

static Stats board_solve(uint32_t cand, uint32_t cols, uint32_t ld,
                         uint32_t rd, uint32_t full, uint32_t sols,
                         uint32_t nodes) {
  while (cand != 0u) {
    uint32_t b = cand & (0u - cand);
    uint32_t nc = cols | b;
    if (nc == full) {
      sols += 1u;
      nodes += 1u;
    } else {
      uint32_t nl = (ld | b) << 1;
      uint32_t nr = (rd | b) >> 1;
      Stats w = board_solve(full & ~(nc | nl | nr), nc, nl, nr, full, sols,
                            nodes + 1u);
      sols = w.sols;
      nodes = w.nodes;
    }
    cand -= b;
  }
  return (Stats){sols, nodes};
}

// one 4-row prefix: decode the column quad, filter illegal placements,
// solve the remaining rows
static Stats prefix_solve(uint32_t j, uint32_t nn, uint32_t full,
                          uint32_t bound) {
  uint32_t i = (j * 2654435761u) & 131071u; // fork-order permutation (bijection)
  if (!(i < bound))
    return (Stats){0u, 0u};
  uint32_t nn2 = nn * nn;
  uint32_t b0 = 1u << (i / (nn2 * nn));
  uint32_t b1 = 1u << ((i / nn2) % nn);
  if ((b1 & (b0 | (b0 << 1) | (b0 >> 1))) != 0u)
    return (Stats){0u, 0u};
  uint32_t b2 = 1u << ((i / nn) % nn);
  uint32_t c2 = b0 | b1;
  uint32_t l2 = ((b0 << 1) | b1) << 1;
  uint32_t r2 = ((b0 >> 1) | b1) >> 1;
  if ((b2 & (c2 | l2 | r2)) != 0u)
    return (Stats){0u, 0u};
  uint32_t b3 = 1u << (i % nn);
  uint32_t c3 = c2 | b2;
  uint32_t l3 = (l2 | b2) << 1;
  uint32_t r3 = (r2 | b2) >> 1;
  if ((b3 & (c3 | l3 | r3)) != 0u)
    return (Stats){0u, 0u};
  uint32_t c4 = c3 | b3;
  uint32_t l4 = (l3 | b3) << 1;
  uint32_t r4 = (r3 | b3) >> 1;
  return board_solve(full & ~(c4 | l4 | r4), c4, l4, r4, full, 0u, 0u);
}

int main(void) {
  uint32_t nn = SIZE;
  uint32_t full = (1u << nn) - 1u;
  uint32_t nn2 = nn * nn;
  uint32_t nnnn = nn2 * nn2;
  uint32_t bound = LIMIT < nnnn ? LIMIT : nnnn;
  uint32_t sols = 0u, nodes = 0u;
  for (uint32_t i = 0u; i < (1u << DEPTH); i += 1u) {
    Stats s = prefix_solve(i, nn, full, bound);
    sols += s.sols;
    nodes += s.nodes;
  }
  printf("%u\n", (sols * 2654435761u) ^ nodes);
  return 0;
}
