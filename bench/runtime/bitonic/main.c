// Native C twin of main.bend: same tree-shaped bitonic sorting
// network, key generator and Stat verification scan, single-threaded.
// Tree nodes live in an arena with a freelist (consuming a node in a
// match frees it, mirroring the linear semantics), so peak memory stays
// ~2n nodes across the whole sort.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifndef SIZE
#define SIZE 23
#endif

typedef enum TreeTag { TREE_LEAF, TREE_NODE } TreeTag;
typedef struct Tree {
  uint32_t tag;
  uint32_t a, b; // leaf: a = v; node: a = l, b = r
} Tree;
typedef struct TreeArena {
  Tree *items;
  size_t length, capacity;
  uint32_t free_head; // freelist threaded through .a
} TreeArena;

#define TREE_NIL 0xFFFFFFFFu

static uint32_t tree_arena_push(TreeArena *arena, Tree value) {
  if (arena->free_head != TREE_NIL) {
    uint32_t i = arena->free_head;
    arena->free_head = arena->items[i].a;
    arena->items[i] = value;
    return i;
  }
  if (arena->length == arena->capacity) {
    size_t n = arena->capacity ? arena->capacity * 2 : 1024;
    Tree *p = realloc(arena->items, n * sizeof(*p));
    if (!p) {
      fputs("Tree arena exhausted\n", stderr);
      exit(2);
    }
    arena->items = p;
    arena->capacity = n;
  }
  uint32_t i = (uint32_t)arena->length++;
  arena->items[i] = value;
  return i;
}
static void tree_drop(TreeArena *arena, uint32_t i) {
  arena->items[i].a = arena->free_head;
  arena->free_head = i;
}
static uint32_t tree_leaf(TreeArena *a, uint32_t v) {
  return tree_arena_push(a, (Tree){TREE_LEAF, v, 0});
}
static uint32_t tree_node(TreeArena *a, uint32_t l, uint32_t r) {
  return tree_arena_push(a, (Tree){TREE_NODE, l, r});
}

static uint32_t word_prng(uint32_t x) {
  uint32_t b = x ^ (x << 13);
  uint32_t d = b ^ (b >> 17);
  return d ^ (d << 5);
}
static uint32_t word_key(uint32_t i) { return word_prng((i + 1u) * 2654435761u); }

static uint32_t tree_swap(TreeArena *a, uint32_t s, uint32_t x, uint32_t y) {
  if (s == 0)
    return tree_node(a, tree_leaf(a, x), tree_leaf(a, y));
  return tree_node(a, tree_leaf(a, y), tree_leaf(a, x));
}
static uint32_t tree_warp_zip(TreeArena *a, uint32_t wa, uint32_t wb) {
  Tree p = a->items[wa], q = a->items[wb];
  tree_drop(a, wa);
  tree_drop(a, wb);
  return tree_node(a, tree_node(a, p.a, q.a), tree_node(a, p.b, q.b));
}
static uint32_t tree_warp(TreeArena *a, uint32_t s, uint32_t x, uint32_t y) {
  Tree p = a->items[x], q = a->items[y];
  tree_drop(a, x);
  tree_drop(a, y);
  if (p.tag == TREE_LEAF) {
    uint32_t av = p.a, bv = q.a;
    return tree_swap(a, s ^ (av > bv ? 1u : 0u), av, bv);
  }
  uint32_t wa = tree_warp(a, s, p.a, q.a);
  uint32_t wb = tree_warp(a, s, p.b, q.b);
  return tree_warp_zip(a, wa, wb);
}
// mode 0 warps the halves, mode 1 descends one level shallower
static uint32_t tree_flow(TreeArena *a, uint32_t d, uint32_t m, uint32_t s,
                          uint32_t t) {
  if (d == 0)
    return t;
  Tree n = a->items[t];
  if (m == 0) {
    tree_drop(a, t);
    uint32_t w = tree_warp(a, s, n.a, n.b);
    return tree_flow(a, d - 1, 1, s, w);
  }
  tree_drop(a, t);
  uint32_t fa = tree_flow(a, d, 0, s, n.a);
  uint32_t fb = tree_flow(a, d, 0, s, n.b);
  return tree_node(a, fa, fb);
}
static uint32_t tree_sort_1(TreeArena *a, uint32_t d, uint32_t s, uint32_t sa,
                            uint32_t sb) {
  return tree_flow(a, d, 0, s, tree_node(a, sa, sb));
}
static uint32_t tree_bsort(TreeArena *a, uint32_t d, uint32_t s, uint32_t x) {
  if (d == 0)
    return tree_leaf(a, word_key(x));
  uint32_t sa = tree_bsort(a, d - 1, 0, x * 2 + 1);
  uint32_t sb = tree_bsort(a, d - 1, 1, x * 2);
  return tree_sort_1(a, d, s, sa, sb);
}

typedef struct Stat {
  uint32_t lo, hi, ok, mx;
} Stat;
static Stat stat_join(Stat a, Stat b) {
  return (Stat){a.lo, b.hi, (a.ok & b.ok) & (a.hi <= b.lo ? 1u : 0u),
                a.mx * 2654435761u + b.mx};
}
static Stat tree_scan(TreeArena *a, uint32_t d, uint32_t t) {
  Tree n = a->items[t];
  tree_drop(a, t);
  if (d == 0) {
    uint32_t v = n.a;
    return (Stat){v, v, 1, v};
  }
  Stat l = tree_scan(a, d - 1, n.a);
  Stat r = tree_scan(a, d - 1, n.b);
  return stat_join(l, r);
}
static uint32_t stat_out(Stat s) {
  return ((s.mx * 2654435761u) ^ (s.hi + s.lo * 340573321u)) +
         s.ok * 2246822519u;
}

int main(void) {
  TreeArena arena = {0, 0, 0, TREE_NIL};
  uint32_t t = tree_bsort(&arena, SIZE, 0, 0);
  printf("%u\n", stat_out(tree_scan(&arena, SIZE, t)));
  free(arena.items);
}
