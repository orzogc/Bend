#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef enum StatsTag { STATS_LEAF, STATS_NODE } StatsTag;
typedef struct Stats {
  StatsTag tag;
  uint32_t a, b, c;
} Stats;
typedef struct StatsArena {
  Stats *items;
  size_t length, capacity;
} StatsArena;
static uint32_t stats_arena_push(StatsArena *a, Stats s) {
  if (a->length == a->capacity) {
    size_t n = a->capacity ? a->capacity * 2 : 1024;
    Stats *p = realloc(a->items, n * sizeof(*p));
    if (!p)
      exit(2);
    a->items = p;
    a->capacity = n;
  }
  uint32_t i = (uint32_t)a->length++;
  a->items[i] = s;
  return i;
}
static uint32_t stats_leaf(StatsArena *a, uint32_t x, uint32_t y, uint32_t n) {
  return stats_arena_push(a, (Stats){STATS_LEAF, x, y, n});
}
static uint32_t stats_node(StatsArena *a, uint32_t l, uint32_t r) {
  return stats_arena_push(a, (Stats){STATS_NODE, l, r, 0});
}
static uint32_t word_prng(uint32_t x) {
  uint32_t b = x ^ (x << 13), d = b ^ (b >> 17);
  return d ^ (d << 5);
}
static uint32_t value_select(uint32_t t, uint32_t x, uint32_t y) {
  return t ? y : x;
}
static uint32_t value_min(uint32_t a, uint32_t b) {
  return value_select(a < b, b, a);
}
static uint32_t point_distance(uint32_t x, uint32_t y, uint32_t c, uint32_t k) {
  uint32_t cx = c & 65535, cy = c >> 16;
  uint32_t dx = value_select(x < cx, x - cx, cx - x),
           dy = value_select(y < cy, y - cy, cy - y);
  return ((dx * dx + dy * dy) << 3) | k;
}
static uint32_t stats_zip(StatsArena *a, uint32_t x, uint32_t y) {
  Stats p = a->items[x], q = a->items[y];
  if (p.tag == STATS_LEAF && q.tag == STATS_LEAF)
    return stats_leaf(a, p.a + q.a, p.b + q.b, p.c + q.c);
  if (p.tag == STATS_LEAF)
    return x;
  if (q.tag == STATS_LEAF)
    return x;
  return stats_node(a, stats_zip(a, p.a, q.a), stats_zip(a, p.b, q.b));
}
static uint32_t stats_chunk(StatsArena *a, uint32_t i, const uint32_t c[8]) {
  uint32_t sx[8] = {0}, sy[8] = {0}, nn[8] = {0};
  for (uint32_t j = 64; j; j--) {
    uint32_t h = word_prng((i + j) * 2654435761u), x = h & 1023,
             y = (h >> 16) & 1023;
    uint32_t b =
        value_min(value_min(value_min(point_distance(x, y, c[0], 0),
                                      point_distance(x, y, c[1], 1)),
                            value_min(point_distance(x, y, c[2], 2),
                                      point_distance(x, y, c[3], 3))),
                  value_min(value_min(point_distance(x, y, c[4], 4),
                                      point_distance(x, y, c[5], 5)),
                            value_min(point_distance(x, y, c[6], 6),
                                      point_distance(x, y, c[7], 7)))) &
        7;
    sx[b] += x;
    sy[b] += y;
    nn[b]++;
  }
  uint32_t q[8];
  for (int k = 0; k < 8; k++)
    q[k] = stats_leaf(a, sx[k], sy[k], nn[k]);
  return stats_node(
      a, stats_node(a, stats_node(a, q[0], q[1]), stats_node(a, q[2], q[3])),
      stats_node(a, stats_node(a, q[4], q[5]), stats_node(a, q[6], q[7])));
}
static uint32_t stats_fold(StatsArena *a, uint32_t d, uint32_t i,
                           const uint32_t c[8]) {
  if (!d)
    return stats_chunk(a, i, c);
  uint32_t x = stats_fold(a, d - 1, i, c),
           y = stats_fold(a, d - 1, i + (64u << (d - 1)), c);
  return stats_zip(a, x, y);
}
static uint32_t stats_centroid(StatsArena *a, uint32_t s, uint32_t old) {
  Stats x = a->items[s];
  if (x.tag == STATS_NODE)
    return old;
  uint32_t m = x.c ? x.c : 1, next = x.a / m | ((x.b / m) << 16);
  return x.c ? next : old;
}
static void stats_split(StatsArena *a, uint32_t s, uint32_t *out) {
  Stats x = a->items[s];
  if (x.tag == STATS_NODE) {
    out[0] = x.a;
    out[1] = x.b;
  } else {
    out[0] = s;
    out[1] = stats_leaf(a, 0, 0, 0);
  }
}
static void centroids_step(uint32_t d, uint32_t c[8], StatsArena *a) {
  a->length = 0;
  uint32_t root = stats_fold(a, d - 6, 0, c), p[2], q[4], z[8];
  stats_split(a, root, p);
  stats_split(a, p[0], q);
  stats_split(a, p[1], q + 2);
  for (int i = 0; i < 4; i++)
    stats_split(a, q[i], z + 2 * i);
  for (int i = 0; i < 8; i++)
    c[i] = stats_centroid(a, z[i], c[i]);
}
static uint32_t centroid_initial(uint32_t k) {
  uint32_t h = word_prng(12345 + k);
  return (h & 1023) | (((h >> 16) & 1023) << 16);
}
static uint32_t restart_run(uint32_t r, uint32_t d) {
  uint32_t c[8];
  for (int k = 0; k < 8; k++)
    c[k] = centroid_initial(r * 8 + k + 1);
  StatsArena a = {0};
  for (int n = 0; n < 20; n++)
    centroids_step(d, c, &a);
  free(a.items);
  uint32_t h = c[0];
  for (int k = 1; k < 8; k++)
    h = h * 2654435761u + c[k];
  return h;
}
static uint32_t restart_batch(uint32_t b, uint32_t r, uint32_t d) {
  if (!b)
    return restart_run(r, d);
  return restart_batch(b - 1, r, d) +
         restart_batch(b - 1, r + (1u << (b - 1)), d);
}
int main(void) { printf("%u\n", restart_batch(6, 0, 19)); }
