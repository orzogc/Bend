// Native C twin of main.bend: recursive block matrix multiply over
// quad-trees with a Freivalds verification pass. Single-threaded, 1-to-1
// with the Bend program: same quad-tree/vector datatypes, same recursive
// block multiply (8 products joined by 4 adds per node), same numerics in
// wrapping u32. ADT nodes live in a pool arena with a freelist: adds
// consume (free) their inputs, generators and multiplies allocate.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct Node {
  uint32_t tag; // 0 = leaf, 1 = branch
  uint32_t v;
  struct Node *k[4];
} Node;

typedef struct Node Mat;
typedef struct Node Vec;

static Node *pool_free = NULL;
static Node *pool_block = NULL;
static size_t pool_used = 0;
static size_t pool_cap = 0;

static Node *node_alloc(void) {
  if (pool_free != NULL) {
    Node *node = pool_free;
    pool_free = node->k[0];
    return node;
  }
  if (pool_used == pool_cap) {
    pool_cap = 1u << 20;
    pool_block = malloc(pool_cap * sizeof(Node));
    if (pool_block == NULL) {
      fputs("pool exhausted\n", stderr);
      exit(2);
    }
    pool_used = 0;
  }
  return &pool_block[pool_used++];
}

static void node_free(Node *node) {
  node->k[0] = pool_free;
  pool_free = node;
}

static void tree_free(Node *node) {
  if (node->tag != 0u) {
    tree_free(node->k[0]);
    tree_free(node->k[1]);
    if (node->k[2] != NULL) {
      tree_free(node->k[2]);
      tree_free(node->k[3]);
    }
  }
  node_free(node);
}

static Node *node_leaf(uint32_t v) {
  Node *node = node_alloc();
  node->tag = 0u;
  node->v = v;
  return node;
}

static Mat *mat_quad(Mat *a, Mat *b, Mat *c, Mat *d) {
  Node *node = node_alloc();
  node->tag = 1u;
  node->k[0] = a;
  node->k[1] = b;
  node->k[2] = c;
  node->k[3] = d;
  return node;
}

static Vec *vec_branch(Vec *l, Vec *r) {
  Node *node = node_alloc();
  node->tag = 1u;
  node->k[0] = l;
  node->k[1] = r;
  node->k[2] = NULL;
  node->k[3] = NULL;
  return node;
}

static Mat *mat_gen(uint32_t d, uint32_t s) {
  if (d == 0u) {
    return node_leaf(s % 100u);
  }
  Mat *a = mat_gen(d - 1u, s * 1664525u + 1u);
  Mat *b = mat_gen(d - 1u, s * 214013u + 3u);
  Mat *c = mat_gen(d - 1u, s * 16843009u + 5u);
  Mat *e = mat_gen(d - 1u, s * 48271u + 7u);
  return mat_quad(a, b, c, e);
}

static Vec *vec_gen(uint32_t d, uint32_t s) {
  if (d == 0u) {
    return node_leaf((s * 2654435761u) % 100u + 1u);
  }
  Vec *l = vec_gen(d - 1u, s * 1664525u + 1u);
  Vec *r = vec_gen(d - 1u, s * 214013u + 3u);
  return vec_branch(l, r);
}

// consumes both inputs
static Mat *mat_add(Mat *a, Mat *b) {
  if (a->tag == 0u) {
    uint32_t v = a->v + b->v;
    node_free(a);
    node_free(b);
    return node_leaf(v);
  }
  Mat *r0 = mat_add(a->k[0], b->k[0]);
  Mat *r1 = mat_add(a->k[1], b->k[1]);
  Mat *r2 = mat_add(a->k[2], b->k[2]);
  Mat *r3 = mat_add(a->k[3], b->k[3]);
  node_free(a);
  node_free(b);
  return mat_quad(r0, r1, r2, r3);
}

// join of one mul burst: C_ij = P_ij + Q_ij (consumes all eight)
static Mat *mat_add4(Mat *p0, Mat *q0, Mat *p1, Mat *q1, Mat *p2, Mat *q2,
                     Mat *p3, Mat *q3) {
  Mat *c0 = mat_add(p0, q0);
  Mat *c1 = mat_add(p1, q1);
  Mat *c2 = mat_add(p2, q2);
  Mat *c3 = mat_add(p3, q3);
  return mat_quad(c0, c1, c2, c3);
}

// reads both inputs; each node spawns its whole 8-product burst
static Mat *mat_mul(Mat *a, Mat *b) {
  if (a->tag == 0u) {
    return node_leaf(a->v * b->v);
  }
  Mat *p0 = mat_mul(a->k[0], b->k[0]);
  Mat *q0 = mat_mul(a->k[1], b->k[2]);
  Mat *p1 = mat_mul(a->k[0], b->k[1]);
  Mat *q1 = mat_mul(a->k[1], b->k[3]);
  Mat *p2 = mat_mul(a->k[2], b->k[0]);
  Mat *q2 = mat_mul(a->k[3], b->k[2]);
  Mat *p3 = mat_mul(a->k[2], b->k[1]);
  Mat *q3 = mat_mul(a->k[3], b->k[3]);
  return mat_add4(p0, q0, p1, q1, p2, q2, p3, q3);
}

// consumes both inputs
static Vec *vec_add(Vec *x, Vec *y) {
  if (x->tag == 0u) {
    uint32_t v = x->v + y->v;
    node_free(x);
    node_free(y);
    return node_leaf(v);
  }
  Vec *l = vec_add(x->k[0], y->k[0]);
  Vec *r = vec_add(x->k[1], y->k[1]);
  node_free(x);
  node_free(y);
  return vec_branch(l, r);
}

// join of one mvm burst (consumes all four)
static Vec *vec_add2(Vec *t0, Vec *t1, Vec *t2, Vec *t3) {
  return vec_branch(vec_add(t0, t1), vec_add(t2, t3));
}

// reads both inputs; [[a,b],[c,d]] * (l,h) = (a*l + b*h, c*l + d*h)
static Vec *mat_vec_mul(Mat *m, Vec *v) {
  if (m->tag == 0u) {
    return node_leaf(m->v * v->v);
  }
  Vec *t0 = mat_vec_mul(m->k[0], v->k[0]);
  Vec *t1 = mat_vec_mul(m->k[1], v->k[1]);
  Vec *t2 = mat_vec_mul(m->k[2], v->k[0]);
  Vec *t3 = mat_vec_mul(m->k[3], v->k[1]);
  return vec_add2(t0, t1, t2, t3);
}

static uint32_t mat_cksum(Mat *m) {
  if (m->tag == 0u) {
    return m->v;
  }
  uint32_t p = mat_cksum(m->k[0]);
  uint32_t q = mat_cksum(m->k[1]);
  uint32_t r = mat_cksum(m->k[2]);
  uint32_t s = mat_cksum(m->k[3]);
  return p + q + r + s;
}

// or-fold of elementwise xor: 0 iff the vectors are identical
static uint32_t vec_dif(Vec *x, Vec *y) {
  if (x->tag == 0u) {
    return x->v ^ y->v;
  }
  uint32_t l = vec_dif(x->k[0], y->k[0]);
  uint32_t r = vec_dif(x->k[1], y->k[1]);
  return l | r;
}

// one round: generate A, B, r; C = A*B; Freivalds-verify C*r == A*(B*r)
static uint32_t round_run(uint32_t d, uint32_t s) {
  Mat *a = mat_gen(d, s + 1u);
  Mat *b = mat_gen(d, s + 2u);
  Vec *r = vec_gen(d, s + 3u);
  Mat *c = mat_mul(a, b);
  uint32_t k = mat_cksum(c);
  Vec *t1 = mat_vec_mul(c, r);
  Vec *u = mat_vec_mul(b, r);
  Vec *t2 = mat_vec_mul(a, u);
  uint32_t v = vec_dif(t1, t2);
  tree_free(a);
  tree_free(b);
  tree_free(r);
  tree_free(c);
  tree_free(t1);
  tree_free(u);
  tree_free(t2);
  return (k ^ (s * 2654435761u)) + (v == 0u ? 1u : 0u);
}

// batch over the round index space: round i runs on seed = hashed index
// (rounds past nchain contribute zero; u32 addition commutes, so the
// flat loop equals the Bend fork tree's sum)
static uint32_t batch_run(uint32_t nchain, uint32_t d) {
  uint32_t acc = 0u;
  for (uint32_t i = 0u; i < nchain; ++i) {
    acc += round_run(d, i * 2654435761u);
  }
  return acc;
}

int main(void) {
  uint32_t size = 7u;
  uint32_t nchain = 384u;
  printf("%u\n", batch_run(nchain, size));
  return 0;
}
