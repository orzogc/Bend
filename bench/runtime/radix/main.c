// Native C twin of main.bend: same trie sort (gen -> to_map/merge
// -> to_arr) and Chk verification scan, single-threaded. ADT nodes live
// in arenas with freelists (consuming a node in a match frees it,
// mirroring the linear semantics), so peak memory tracks the live
// input tree + trie.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifndef DEPTH
#define DEPTH 22
#endif

#define ARENA_NIL 0xFFFFFFFFu

typedef enum ArrTag { ARR_EMPTY, ARR_SINGLE, ARR_CONCAT } ArrTag;
typedef struct Arr {
  uint32_t tag;
  uint32_t a, b;
} Arr;
typedef enum MapTag { MAP_FREE, MAP_BUSY, MAP_NODE } MapTag;
typedef struct Map {
  uint32_t tag;
  uint32_t left, right;
} Map;
typedef struct ArrArena {
  Arr *items;
  size_t length, capacity;
  uint32_t free_head; // freelist threaded through .a
} ArrArena;
typedef struct MapArena {
  Map *items;
  size_t length, capacity;
  uint32_t free_head; // freelist threaded through .left
} MapArena;

static uint32_t arr_arena_push(ArrArena *arena, Arr value) {
  if (arena->free_head != ARENA_NIL) {
    uint32_t i = arena->free_head;
    arena->free_head = arena->items[i].a;
    arena->items[i] = value;
    return i;
  }
  if (arena->length == arena->capacity) {
    size_t n = arena->capacity ? arena->capacity * 2 : 1024;
    Arr *p = realloc(arena->items, n * sizeof(*p));
    if (!p) {
      fputs("Arr arena exhausted\n", stderr);
      exit(2);
    }
    arena->items = p;
    arena->capacity = n;
  }
  uint32_t i = (uint32_t)arena->length++;
  arena->items[i] = value;
  return i;
}
static void arr_drop(ArrArena *arena, uint32_t i) {
  arena->items[i].a = arena->free_head;
  arena->free_head = i;
}
static uint32_t map_arena_push(MapArena *arena, Map value) {
  if (arena->free_head != ARENA_NIL) {
    uint32_t i = arena->free_head;
    arena->free_head = arena->items[i].left;
    arena->items[i] = value;
    return i;
  }
  if (arena->length == arena->capacity) {
    size_t n = arena->capacity ? arena->capacity * 2 : 1024;
    Map *p = realloc(arena->items, n * sizeof(*p));
    if (!p) {
      fputs("Map arena exhausted\n", stderr);
      exit(2);
    }
    arena->items = p;
    arena->capacity = n;
  }
  uint32_t i = (uint32_t)arena->length++;
  arena->items[i] = value;
  return i;
}
static void map_drop(MapArena *arena, uint32_t i) {
  arena->items[i].left = arena->free_head;
  arena->free_head = i;
}
// deep drop of a discarded subtree (the Mnode-vs-Busy merge arms)
static void map_drop_deep(MapArena *arena, uint32_t i) {
  Map x = arena->items[i];
  map_drop(arena, i);
  if (x.tag == MAP_NODE) {
    map_drop_deep(arena, x.left);
    map_drop_deep(arena, x.right);
  }
}
static uint32_t arr_empty(ArrArena *a) {
  return arr_arena_push(a, (Arr){ARR_EMPTY, 0, 0});
}
static uint32_t arr_single(ArrArena *a, uint32_t x) {
  return arr_arena_push(a, (Arr){ARR_SINGLE, x, 0});
}
static uint32_t arr_concat(ArrArena *a, uint32_t l, uint32_t r) {
  return arr_arena_push(a, (Arr){ARR_CONCAT, l, r});
}
static uint32_t map_free(MapArena *a) {
  return map_arena_push(a, (Map){MAP_FREE, 0, 0});
}
static uint32_t map_busy(MapArena *a) {
  return map_arena_push(a, (Map){MAP_BUSY, 0, 0});
}
static uint32_t map_node(MapArena *a, uint32_t l, uint32_t r) {
  return map_arena_push(a, (Map){MAP_NODE, l, r});
}

static uint32_t word_prng(uint32_t x) {
  uint32_t b = x ^ (x << 13);
  uint32_t d = b ^ (b >> 17);
  return d ^ (d << 5);
}
static uint32_t word_key(uint32_t i) {
  return word_prng((i + 1u) * 2654435761u) & 16777215u;
}

static uint32_t map_merge(MapArena *a, uint32_t x, uint32_t y) {
  Map p = a->items[x], q = a->items[y];
  if (p.tag == MAP_FREE) {
    map_drop(a, x);
    return y;
  }
  if (q.tag == MAP_FREE) {
    map_drop(a, y);
    return x;
  }
  if (p.tag == MAP_BUSY) {
    map_drop(a, x);
    if (q.tag == MAP_NODE)
      map_drop_deep(a, y);
    else
      map_drop(a, y);
    return map_busy(a);
  }
  if (q.tag == MAP_BUSY) {
    map_drop_deep(a, x);
    map_drop(a, y);
    return map_busy(a);
  }
  map_drop(a, x);
  map_drop(a, y);
  uint32_t l = map_merge(a, p.left, q.left);
  uint32_t r = map_merge(a, p.right, q.right);
  return map_node(a, l, r);
}
static uint32_t arr_generate(ArrArena *a, uint32_t n, uint32_t x) {
  if (!n)
    return arr_single(a, word_key(x));
  return arr_concat(a, arr_generate(a, n - 1, x * 2),
                    arr_generate(a, n - 1, x * 2 + 1));
}
static uint32_t map_swap_bits(MapArena *a, uint32_t n, uint32_t x0,
                              uint32_t x1) {
  return n == 0 ? map_node(a, x0, x1) : map_node(a, x1, x0);
}
static uint32_t map_radix(MapArena *a, uint32_t i, uint32_t n, uint32_t k,
                          uint32_t r) {
  while (i) {
    r = map_swap_bits(a, n & k, r, map_free(a));
    k *= 2;
    --i;
  }
  return r;
}
static uint32_t arr_to_map(ArrArena *aa, MapArena *ma, uint32_t i) {
  Arr x = aa->items[i];
  arr_drop(aa, i);
  if (x.tag == ARR_EMPTY)
    return map_free(ma);
  if (x.tag == ARR_SINGLE)
    return map_radix(ma, 24, x.a, 1, map_busy(ma));
  uint32_t l = arr_to_map(aa, ma, x.a);
  uint32_t r = arr_to_map(aa, ma, x.b);
  return map_merge(ma, l, r);
}
static uint32_t map_to_arr(MapArena *ma, ArrArena *aa, uint32_t i,
                           uint32_t k) {
  Map x = ma->items[i];
  map_drop(ma, i);
  if (x.tag == MAP_FREE)
    return arr_empty(aa);
  if (x.tag == MAP_BUSY)
    return arr_single(aa, k);
  uint32_t l = map_to_arr(ma, aa, x.left, k * 2);
  uint32_t r = map_to_arr(ma, aa, x.right, k * 2 + 1);
  return arr_concat(aa, l, r);
}
static uint32_t arr_sort(ArrArena *aa, MapArena *ma, uint32_t x) {
  return map_to_arr(ma, aa, arr_to_map(aa, ma, x), 0);
}

typedef struct Chk {
  uint32_t nil; // 1 = Cnil
  uint32_t lo, hi, ok, cnt, sum;
} Chk;
static Chk chk_join(Chk a, Chk b) {
  if (a.nil)
    return b;
  if (b.nil)
    return a;
  return (Chk){0,
               a.lo,
               b.hi,
               (a.ok & b.ok) & (a.hi < b.lo ? 1u : 0u),
               a.cnt + b.cnt,
               a.sum + b.sum};
}
static Chk arr_chk(ArrArena *aa, uint32_t i) {
  Arr x = aa->items[i];
  arr_drop(aa, i);
  if (x.tag == ARR_EMPTY)
    return (Chk){1, 0, 0, 0, 0, 0};
  if (x.tag == ARR_SINGLE)
    return (Chk){0, x.a, x.a, 1, 1, x.a};
  Chk l = arr_chk(aa, x.a);
  Chk r = arr_chk(aa, x.b);
  return chk_join(l, r);
}
static uint32_t chk_out(Chk c) {
  if (c.nil)
    return 0;
  return ((c.sum + c.cnt * 2654435761u) ^ (c.hi + c.lo * 340573321u)) +
         c.ok * 2246822519u;
}

int main(void) {
  ArrArena aa = {0, 0, 0, ARENA_NIL};
  MapArena ma = {0, 0, 0, ARENA_NIL};
  uint32_t x = arr_generate(&aa, DEPTH, 0);
  uint32_t y = arr_sort(&aa, &ma, x);
  printf("%u\n", chk_out(arr_chk(&aa, y)));
  free(aa.items);
  free(ma.items);
}
