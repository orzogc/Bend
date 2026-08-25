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

type Mat:
  Lf{v: U32}
  Qd{a: Mat, b: Mat, c: Mat, d: Mat}

type Vec:
  Vl{v: U32}
  Vn{l: Vec, r: Vec}

# copy witnesses for the shared trees: never emitted, they only
# license +Mat / +Vec
assert Mat.copy:
  forall m: Mat
  Copy(Mat, m) & Copy(Mat, m)

def Mat.copy(m):
  match m:
    case Lf{v}:
      ((v1, e1), (v2, e2)) = U32.copy(v)
      p1 = Equal.cong(U32, Mat, x => Lf{x}, v, v1, e1)
      p2 = Equal.cong(U32, Mat, x => Lf{x}, v, v2, e2)
      ((Lf{v1}, p1), (Lf{v2}, p2))
    case Qd{a, b, c, d}:
      ((a1, ea1), (a2, ea2)) = Mat.copy(a)
      ((b1, eb1), (b2, eb2)) = Mat.copy(b)
      ((c1, ec1), (c2, ec2)) = Mat.copy(c)
      ((d1, ed1), (d2, ed2)) = Mat.copy(d)
      p1 = Equal.trans(Mat, Qd{a, b, c, d}, Qd{a1, b, c, d}, Qd{a1, b1, c1, d1},
                       Equal.cong(Mat, Mat, x => Qd{x, b, c, d}, a, a1, ea1),
                       Equal.trans(Mat, Qd{a1, b, c, d}, Qd{a1, b1, c, d}, Qd{a1, b1, c1, d1},
                                   Equal.cong(Mat, Mat, x => Qd{a1, x, c, d}, b, b1, eb1),
                                   Equal.trans(Mat, Qd{a1, b1, c, d}, Qd{a1, b1, c1, d}, Qd{a1, b1, c1, d1},
                                               Equal.cong(Mat, Mat, x => Qd{a1, b1, x, d}, c, c1, ec1),
                                               Equal.cong(Mat, Mat, x => Qd{a1, b1, c1, x}, d, d1, ed1))))
      p2 = Equal.trans(Mat, Qd{a, b, c, d}, Qd{a2, b, c, d}, Qd{a2, b2, c2, d2},
                       Equal.cong(Mat, Mat, x => Qd{x, b, c, d}, a, a2, ea2),
                       Equal.trans(Mat, Qd{a2, b, c, d}, Qd{a2, b2, c, d}, Qd{a2, b2, c2, d2},
                                   Equal.cong(Mat, Mat, x => Qd{a2, x, c, d}, b, b2, eb2),
                                   Equal.trans(Mat, Qd{a2, b2, c, d}, Qd{a2, b2, c2, d}, Qd{a2, b2, c2, d2},
                                               Equal.cong(Mat, Mat, x => Qd{a2, b2, x, d}, c, c2, ec2),
                                               Equal.cong(Mat, Mat, x => Qd{a2, b2, c2, x}, d, d2, ed2))))
      ((Qd{a1, b1, c1, d1}, p1), (Qd{a2, b2, c2, d2}, p2))

assert Vec.copy:
  forall v: Vec
  Copy(Vec, v) & Copy(Vec, v)

def Vec.copy(v):
  match v:
    case Vl{x}:
      ((x1, e1), (x2, e2)) = U32.copy(x)
      p1 = Equal.cong(U32, Vec, y => Vl{y}, x, x1, e1)
      p2 = Equal.cong(U32, Vec, y => Vl{y}, x, x2, e2)
      ((Vl{x1}, p1), (Vl{x2}, p2))
    case Vn{l, r}:
      ((l1, el1), (l2, el2)) = Vec.copy(l)
      ((r1, er1), (r2, er2)) = Vec.copy(r)
      p1 = Equal.trans(Vec, Vn{l, r}, Vn{l1, r}, Vn{l1, r1},
                       Equal.cong(Vec, Vec, y => Vn{y, r}, l, l1, el1),
                       Equal.cong(Vec, Vec, y => Vn{l1, y}, r, r1, er1))
      p2 = Equal.trans(Vec, Vn{l, r}, Vn{l2, r}, Vn{l2, r2},
                       Equal.cong(Vec, Vec, y => Vn{y, r}, l, l2, el2),
                       Equal.cong(Vec, Vec, y => Vn{l2, y}, r, r2, er2))
      ((Vn{l1, r1}, p1), (Vn{l2, r2}, p2))

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert gen:
  forall +d: +Nat
  forall +s: +U32
  Mat

def gen(d, s):
  match d:
    case 0n:
      Lf{U32.mod(s, 100)}
    case 1n+p:
      a b c e = gen(p, U32.inc(U32.mul(s, 1664525))) gen(p, U32.add(U32.mul(s, 214013), 3)) gen(p, U32.add(U32.mul(s, 16843009), 5)) gen(p, U32.add(U32.mul(s, 48271), 7))
      Qd{a, b, c, e}

assert vgen:
  forall +d: +Nat
  forall +s: +U32
  Vec

def vgen(d, s):
  match d:
    case 0n:
      Vl{U32.inc(U32.mod(U32.mul(s, 2654435761), 100))}
    case 1n+p:
      l r = vgen(p, U32.inc(U32.mul(s, 1664525))) vgen(p, U32.add(U32.mul(s, 214013), 3))
      Vn{l, r}

assert add:
  forall a: Mat
  forall b: Mat
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
assert add4:
  forall p0: Mat
  forall q0: Mat
  forall p1: Mat
  forall q1: Mat
  forall p2: Mat
  forall q2: Mat
  forall p3: Mat
  forall q3: Mat
  Mat

def add4(p0, q0, p1, q1, p2, q2, p3, q3):
  c0 c1 c2 c3 = add(p0, q0) add(p1, q1) add(p2, q2) add(p3, q3)
  Qd{c0, c1, c2, c3}

# each node spawns its whole 8-product burst as ONE 8-way fork,
# then joins through add4's single add burst
assert mul:
  forall +a: +Mat
  forall +b: +Mat
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

assert vadd:
  forall x: Vec
  forall y: Vec
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
assert vadd2:
  forall t0: Vec
  forall t1: Vec
  forall t2: Vec
  forall t3: Vec
  Vec

def vadd2(t0, t1, t2, t3):
  top bot = vadd(t0, t1) vadd(t2, t3)
  Vn{top, bot}

# [[a,b],[c,d]] * (l,h) = (a*l + b*h, c*l + d*h)
assert mvm:
  forall m: Mat
  forall +v: +Vec
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

assert cksum:
  forall m: Mat
  U32

def cksum(m):
  match m:
    case Lf{x}:
      x
    case Qd{a, b, c, d}:
      p q r s = cksum(a) cksum(b) cksum(c) cksum(d)
      U32.add(U32.add(U32.add(p, q), r), s)

# or-fold of elementwise xor: 0 iff the vectors are identical
assert vdif:
  forall x: Vec
  forall y: Vec
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
assert round:
  forall +d: +Nat
  forall +s: +U32
  U32

def round(d, s):
  a00 b00 = gen(d, U32.inc(s)) gen(d, U32.add(s, 2))
  +a = {a00 : +Mat}
  +b = {b00 : +Mat}
  +r = {vgen(d, U32.add(s, 3)) : +Vec}
  +c = {mul(a, b) : +Mat}
  k = cksum(c)
  t1 = mvm(c, r)
  t2 = mvm(a, mvm(b, r))
  U32.add(U32.xor(k, U32.mul(s, 2654435761)), b2u(U32.is_zero(vdif(t1, t2))))

assert batch.leaf:
  forall +pp: +U32
  forall n: U32
  forall d: Nat
  U32

def batch.leaf(pp, n, d):
  match U32.is_lt(pp, n):
    case False{}:
      0
    case True{}:
      round(d, U32.mul(pp, 2654435761))

# batch tree over the round index space: leaf i runs one round when
# p < nchain, p = the leaf's odd-multiplier permuted index (seed =
# hashed p, so the live chain set -- and the checksum -- is the same
# for any spread)
assert batch:
  forall +bg: +Nat
  forall +i: +U32
  forall +n: +U32
  forall +m: +U32
  forall +d: +Nat
  U32

def batch(bg, i, n, m, d):
  match bg:
    case 0n:
      batch.leaf(U32.and(U32.mul(i, 2654435761), m), n, d)
    case 1n+p:
      x y = batch(p, i, n, m, d) batch(p, U32.add(i, U32.shln(p, 1)), n, m, d)
      U32.add(x, y)

assert size:
  Nat

def size():
  7n

assert blog:
  Nat

def blog():
  9n

assert nchain:
  U32

def nchain():
  384

# small: size 3n blog 2n nchain 3 expect 4292995302; big expect 3797651056
assert main:
  IO(Unit)

def main():
  mm = U32.sub(U32.shln(blog(), 1), 1)
  IO.print(U32.show(batch!(blog(), 0, nchain(), mm, size())))
