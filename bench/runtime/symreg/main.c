// par_symreg: single-threaded C twin of main.bend. Same
// algorithms over the same expression-tree ADT: expr_gen materializes
// each depth-5 candidate AST from the xorshift32 stream into a bump
// arena (reset per candidate, no per-node malloc), expr_eval is the
// recursive pattern-matching interpreter (Bend's eval walks the
// tree; the value recursion, order and u32 numerics are identical),
// expr_size adds the parsimony penalty,
// batch_run folds the tournament over the population, seed_climb
// hill-climbs the winner. Checksum printed as one u32.
// Build: clang -O3 -DNDEBUG -ffp-contract=off par_symreg.c -lm
// Expected at SIZE=18, PTS=110: 2383953211.

#include <stdint.h>
#include <stdio.h>

#define SIZE 18u
#define PTS 110u
#define ROUNDS 32u

// Expr ADT: bump arena of tagged nodes (a full depth-5 tree is 63 nodes)
enum { EXPR_VAR, EXPR_LIT, EXPR_ADD, EXPR_SUB, EXPR_MUL, EXPR_XOR };
typedef struct {
  uint32_t tag, a, b;
} Expr;
static Expr expr_arena[64];
static uint32_t expr_arena_len;

static uint32_t expr_push(uint32_t tag, uint32_t a, uint32_t b) {
  uint32_t i = expr_arena_len++;
  expr_arena[i] = (Expr){tag, a, b};
  return i;
}

static uint32_t word_prng(uint32_t x) {
  uint32_t b = x ^ (x << 13);
  uint32_t d = b ^ (b >> 17);
  return d ^ (d << 5);
}

static uint32_t value_select(uint32_t t, uint32_t x, uint32_t y) {
  return t == 0u ? x : y;
}

static uint32_t value_difference(uint32_t a, uint32_t b) {
  return value_select(a < b, a - b, b - a);
}

// materialize a candidate AST straight off the hash stream
static uint32_t expr_gen(uint32_t d, uint32_t h) {
  if (d == 0u) {
    if (((h >> 8) & 1u) == 0u)
      return expr_push(EXPR_VAR, 0u, 0u);
    return expr_push(EXPR_LIT, h & 255u, 0u);
  }
  uint32_t a = expr_gen(d - 1u, word_prng(h ^ 2654435761u));
  uint32_t b = expr_gen(d - 1u, word_prng(h + 340573321u));
  switch (h % 4u) {
  case 0u:
    return expr_push(EXPR_ADD, a, b);
  case 1u:
    return expr_push(EXPR_SUB, a, b);
  case 2u:
    return expr_push(EXPR_MUL, a, b);
  default:
    return expr_push(EXPR_XOR, a, b);
  }
}

// pattern-matching interpreter: value of the candidate at x
static uint32_t expr_eval(uint32_t e, uint32_t x) {
  Expr n = expr_arena[e];
  switch (n.tag) {
  case EXPR_VAR:
    return x;
  case EXPR_LIT:
    return n.a;
  case EXPR_ADD:
    return expr_eval(n.a, x) + expr_eval(n.b, x);
  case EXPR_SUB:
    return expr_eval(n.a, x) - expr_eval(n.b, x);
  case EXPR_MUL:
    return expr_eval(n.a, x) * expr_eval(n.b, x);
  default:
    return expr_eval(n.a, x) ^ expr_eval(n.b, x);
  }
}

// parsimony: AST node count
static uint32_t expr_size(uint32_t e) {
  Expr n = expr_arena[e];
  if (n.tag == EXPR_VAR || n.tag == EXPR_LIT)
    return 1u;
  return 1u + (expr_size(n.a) + expr_size(n.b));
}

// dataset fold: error sum over x = 0..j-1, then the parsimony penalty
static uint32_t fitness_loop(uint32_t j, uint32_t e, uint32_t acc) {
  while (j != 0u) {
    uint32_t x = j - 1u;
    uint32_t p = expr_eval(e, x);
    uint32_t t = x * x + (3u * x + 7u);
    acc += value_difference(p, t);
    j = x;
  }
  return acc + expr_size(e) * 8u;
}

typedef struct {
  uint32_t fit, seed, sum;
} Sel;

static Sel candidate_evaluate(uint32_t s, uint32_t pts) {
  expr_arena_len = 0u;
  uint32_t t = expr_gen(5u, word_prng(s));
  uint32_t f = fitness_loop(pts, t, 0u);
  return (Sel){f, s, f ^ (s * 2654435761u)};
}

// tournament: keep the lower-fitness candidate, sum the checksums
static Sel winner_pick(Sel a, Sel b) {
  uint32_t w = a.fit < b.fit;
  return (Sel){value_select(w, b.fit, a.fit), value_select(w, b.seed, a.seed),
               a.sum + b.sum};
}

static Sel batch_run(uint32_t d, uint32_t s, uint32_t pts) {
  if (d == 0u)
    return candidate_evaluate(word_prng(s), pts);
  Sel a = batch_run(d - 1u, s * 1664525u + 1u, pts);
  Sel b = batch_run(d - 1u, s * 214013u + 3u, pts);
  return winner_pick(a, b);
}

// hill-climb the tournament winner: mutate the seed, keep improvements
static uint32_t seed_climb(uint32_t r, uint32_t bs, uint32_t bf,
                           uint32_t pts) {
  while (r != 0u) {
    Sel w0 = candidate_evaluate(word_prng(bs ^ (r * 40503u)), pts);
    uint32_t w = w0.fit < bf;
    bs = value_select(w, bs, w0.seed);
    bf = value_select(w, bf, w0.fit);
    r -= 1u;
  }
  return bf ^ (bs * 2654435761u);
}

int main(void) {
  Sel w1 = batch_run(SIZE, 42u, PTS);
  printf("%u\n", seed_climb(ROUNDS, w1.seed, w1.fit, PTS) + w1.sum);
  return 0;
}
