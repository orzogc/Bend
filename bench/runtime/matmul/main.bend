import Base
# Matmul: recursive block matrix multiply over quad-trees, with a
# Freivalds verification pass, ported 1-to-1 from Bend3's
# par_tree_mat_mul (Bend3's own(x) boxes drop -- Bend4 spells the
# shares as + binders).
# 2^blog slots fork as a balanced batch tree; each live leaf runs one
# round: generate two pseudo-random 2^size x 2^size matrices as
# depth-size quad-trees, multiply them block-recursively (each node
# spawns its whole 8-product burst as ONE 8-way fork), then verify
# C = A*B by Freivalds' check: fold |C*r - A*(B*r)| over a random
# vector r (exact in wrapping u32, so the or-fold is 0 iff the product
# is right). Round checksums mix the matrix fold with the verification
# bit and sum up the fork tree. Depth counters
# are Nats (no U32 match in Bend4). This bench clones heap values: mul
# and round share whole Mat/Vec trees through + binders.
#
# Sizes (size, blog, nchain): small (3, 2, 3) expect 4292995302
# (verified against a Bend3 C run on the cluster), big (7, 9, 384)
# expect 3797651056 (from the Bend3 header).

type Mat is Data:
  Lf{v: U32}
  Qd{a: Mat, b: Mat, c: Mat, d: Mat}

type Vec is Data:
  Vl{v: U32}
  Vn{l: Vec, r: Vec}

law b2u:
  for b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

law gen:
  for +d: Nat
  for +s: U32
  Mat

def gen(d, s):
  match d:
    case 0n:
      Lf{U32.mod(s, 100)}
    case 1n+p:
      a b c e = gen(p, U32.inc(U32.mul(s, 1664525))) gen(p, U32.add(U32.mul(s, 214013), 3)) gen(p, U32.add(U32.mul(s, 16843009), 5)) gen(p, U32.add(U32.mul(s, 48271), 7))
      Qd{a, b, c, e}

law vgen:
  for +d: Nat
  for +s: U32
  Vec

def vgen(d, s):
  match d:
    case 0n:
      Vl{U32.inc(U32.mod(U32.mul(s, 2654435761), 100))}
    case 1n+p:
      l r = vgen(p, U32.inc(U32.mul(s, 1664525))) vgen(p, U32.add(U32.mul(s, 214013), 3))
      Vn{l, r}

law add:
  for a: Mat
  for b: Mat
  Mat

def add(a, b):
  match a b:
    case Lf{x} Lf{y}:
      Lf{U32.add(x, y)}
    case Lf{x} Qd{b0, b1, b2, b3}:
      Lf{0}
    case Qd{a0, a1, a2, a3} Lf{y}:
      Lf{0}
    case Qd{a0, a1, a2, a3} Qd{b0, b1, b2, b3}:
      r0 r1 r2 r3 = add(a0, b0) add(a1, b1) add(a2, b2) add(a3, b3)
      Qd{r0, r1, r2, r3}

# join of one mul burst: C_ij = P_ij + Q_ij, all four quadrant sums
# in one balanced fork
law add4:
  for p0: Mat
  for q0: Mat
  for p1: Mat
  for q1: Mat
  for p2: Mat
  for q2: Mat
  for p3: Mat
  for q3: Mat
  Mat

def add4(p0, q0, p1, q1, p2, q2, p3, q3):
  c0 c1 c2 c3 = add(p0, q0) add(p1, q1) add(p2, q2) add(p3, q3)
  Qd{c0, c1, c2, c3}

# each node spawns its whole 8-product burst as ONE 8-way fork,
# then joins through add4's single add burst
law mul:
  for +a: Mat
  for +b: Mat
  Mat

def mul(a, b):
  match a b:
    case Lf{x} Lf{y}:
      Lf{U32.mul(x, y)}
    case Lf{x} Qd{b0, b1, b2, b3}:
      Lf{0}
    case Qd{a0, a1, a2, a3} Lf{y}:
      Lf{0}
    case Qd{a0, a1, a2, a3} Qd{b0, b1, b2, b3}:
      p0 q0 p1 q1 p2 q2 p3 q3 = mul(a0, b0) mul(a1, b2) mul(a0, b1) mul(a1, b3) mul(a2, b0) mul(a3, b2) mul(a2, b1) mul(a3, b3)
      add4(p0, q0, p1, q1, p2, q2, p3, q3)

law vadd:
  for x: Vec
  for y: Vec
  Vec

def vadd(x, y):
  match x y:
    case Vl{a} Vl{b}:
      Vl{U32.add(a, b)}
    case Vl{a} Vn{c, d}:
      Vl{0}
    case Vn{a, b} Vl{c}:
      Vl{0}
    case Vn{a, b} Vn{c, d}:
      l r = vadd(a, c) vadd(b, d)
      Vn{l, r}

# join of one mvm burst: both half-sums in one fork
law vadd2:
  for t0: Vec
  for t1: Vec
  for t2: Vec
  for t3: Vec
  Vec

def vadd2(t0, t1, t2, t3):
  top bot = vadd(t0, t1) vadd(t2, t3)
  Vn{top, bot}

# [[a,b],[c,d]] * (l,h) = (a*l + b*h, c*l + d*h)
law mvm:
  for m: Mat
  for +v: Vec
  Vec

def mvm(m, v):
  match m v:
    case Lf{x} Vl{y}:
      Vl{U32.mul(x, y)}
    case Lf{x} Vn{l, h}:
      Vl{0}
    case Qd{a, b, c, d} Vl{y}:
      Vl{0}
    case Qd{a, b, c, d} Vn{l, h}:
      t0 t1 t2 t3 = mvm(a, l) mvm(b, h) mvm(c, l) mvm(d, h)
      vadd2(t0, t1, t2, t3)

law cksum:
  for m: Mat
  U32

def cksum(m):
  match m:
    case Lf{x}:
      x
    case Qd{a, b, c, d}:
      p q r s = cksum(a) cksum(b) cksum(c) cksum(d)
      U32.add(U32.add(U32.add(p, q), r), s)

# or-fold of elementwise xor: 0 iff the vectors are identical
law vdif:
  for x: Vec
  for y: Vec
  U32

def vdif(x, y):
  match x y:
    case Vl{a} Vl{b}:
      U32.xor(a, b)
    case Vl{a} Vn{c, d}:
      1
    case Vn{a, b} Vl{c}:
      1
    case Vn{a, b} Vn{c, d}:
      l r = vdif(a, c) vdif(b, d)
      U32.or(l, r)

# one round: generate A, B, r; C = A*B; Freivalds-verify C*r == A*(B*r)
law round:
  for +d: Nat
  for +s: U32
  U32

def round(d, s):
  a00 b00 = gen(d, U32.inc(s)) gen(d, U32.add(s, 2))
  +a = a00
  +b = b00
  +r = vgen(d, U32.add(s, 3))
  +c = mul(a, b)
  k = cksum(c)
  t1 = mvm(c, r)
  t2 = mvm(a, mvm(b, r))
  U32.add(U32.xor(k, U32.mul(s, 2654435761)), b2u(U32.is_zero(vdif(t1, t2))))

law batch.leaf.go:
  for t: Bool
  for d: Nat
  for pp: U32
  U32

law batch.leaf:
  for +pp: U32
  for n: U32
  for d: Nat
  U32

def batch.leaf.go(t, d, pp):
  match t:
    case False{}:
      0
    case True{}:
      round(d, U32.mul(pp, 2654435761))

def batch.leaf(pp, n, d):
  batch.leaf.go(U32.is_lt(pp, n), d, pp)

# batch tree over the round index space: leaf i runs one round when
# p < nchain, p = the leaf's odd-multiplier permuted index (seed =
# hashed p, so the live chain set -- and the checksum -- is the same
# for any spread)
law batch:
  for +bg: Nat
  for +i: U32
  for +n: U32
  for +m: U32
  for +d: Nat
  U32

def batch(bg, i, n, m, d):
  match bg:
    case 0n:
      batch.leaf(U32.and(U32.mul(i, 2654435761), m), n, d)
    case 1n+p:
      x y = batch(p, i, n, m, d) batch(p, U32.add(i, U32.shln(1, p)), n, m, d)
      U32.add(x, y)

law size:
  Nat

def size():
  7n

law blog:
  Nat

def blog():
  9n

law nchain:
  U32

def nchain():
  384

# small: size 3n blog 2n nchain 3 expect 4292995302; big expect 3797651056
law main:
  IO(Unit)

def main():
  mm = U32.sub(U32.shln(1, blog()), 1)
  IO.print(U32.show(batch!(blog(), 0, nchain(), mm, size())))
