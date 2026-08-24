#[halts]
# the whole-book sharing witness: main pairs bubble's digest with a tiny
# def that KEEPS a (U32 & U32) tuple binder (+p, read twice); that lone
# kept binder flips tocl's shared Tup representation for the WHOLE book,
# and bubble's unshared (Array<F32> & F32) reads collapse (653 -> 3);
# drop the + (single use) and the same book answers 653; distilled from
# the run_bubble_sort_array + run_rle_roundtrip merged-book divergence
# (the runner's note: retries); no interp lane (Base's F32 axioms stuck)
import Base

assert fl:
  forall n: U32
  forall d: U32
  F32

def fl(n, d):
  F32.div(U32.to_f32(n), U32.to_f32(d))

assert rd:
  forall m: Array<F32>
  forall +j: U32
  (Array<F32> & F32)

def rd(m, j):
  (m2, v0) = Array.swap(F32, m, j, fl(0, 1))
  +v = v0
  (m3, z) = Array.swap(F32, m2, j, v)
  (m3, v)

assert swp:
  forall +j: U32
  forall m: Array<F32>
  Array<F32>

def swp(j, m):
  (m1, a) = rd(m, j)
  swp.b(j, a, m1)

assert swp.b:
  forall +j: U32
  forall a: F32
  forall m: Array<F32>
  Array<F32>

def swp.b(j, a, m):
  (m2, b) = rd(m, U32.add(j, 1))
  swp.c(j, a, b, m2)

assert swp.c:
  forall +j: U32
  forall +a: F32
  forall +b: F32
  forall m: Array<F32>
  Array<F32>

def swp.c(j, a, b, m):
  match F32.is_lt(b, a):
    case False{}:
      m
    case True{}:
      swp.d(j, a, b, m)

assert swp.d:
  forall +j: U32
  forall a: F32
  forall b: F32
  forall m: Array<F32>
  Array<F32>

def swp.d(j, a, b, m):
  (m2, o1) = Array.swap(F32, m, j, b)
  (m3, o2) = Array.swap(F32, m2, U32.add(j, 1), a)
  m3

assert pass:
  forall +j: Nat
  forall m: Array<F32>
  Array<F32>

def pass(j, m):
  match j:
    case 0n:
      m
    case 1n+p:
      pass(p, swp(U32.sub(3, U32.add(U32.from_nat(p), 1)), m))

assert rounds:
  forall r: Nat
  forall m: Array<F32>
  Array<F32>

def rounds(r, m):
  match r:
    case 0n:
      m
    case 1n+p:
      rounds(p, pass(3n, m))

assert build:
  Array<F32>

def build():
  {ANode{ANode{ALeaf{fl(7, 2)}, ALeaf{fl(5, 2)}}, ANode{ALeaf{fl(5, 4)}, ALeaf{fl(1, 2)}}} : Array<F32>}

assert digest:
  forall m: Array<F32>
  U32

def digest(m):
  (m1, a) = rd(m, 0)
  digest.b(a, m1)

assert digest.b:
  forall a: F32
  forall m: Array<F32>
  U32

def digest.b(a, m):
  (m2, b) = rd(m, 1)
  digest.c(a, b, m2)

assert digest.c:
  forall a: F32
  forall b: F32
  forall m: Array<F32>
  U32

def digest.c(a, b, m):
  (m3, c) = rd(m, 2)
  digest.d(a, b, c, m3)

assert digest.d:
  forall a: F32
  forall b: F32
  forall c: F32
  forall m: Array<F32>
  U32

def digest.d(a, b, c, m):
  (m4, d) = rd(m, 3)
  digest.e(a, b, c, d, m4)

assert digest.e:
  forall a: F32
  forall b: F32
  forall c: F32
  forall d: F32
  forall m: Array<F32>
  U32

def digest.e(a, b, c, d, m):
  F32.to_u32(F32.add(F32.add(F32.add(F32.mul(a, fl(1000, 1)), F32.mul(b, fl(100, 1))), F32.mul(c, fl(10, 1))), d))

assert fst:
  forall p: (U32 & U32)
  U32

def fst(p):
  (a, b) = p
  a

assert mkp:
  (U32 & U32)

def mkp():
  (2, 7)

assert keept:
  forall +p: (U32 & U32)
  U32

def keept(p):
  U32.add(fst(p), fst(p))

assert main.out:
  (U32 & U32)

def main.out():
  (digest(rounds(3n, build())), keept(mkp()))

assert main:
  IO(Unit)

def main():
  Tuple{a, b} = main.out()
  s = String.append(U32.show(a), String.append(", ", String.append(U32.show(b), "}")))
  IO.print(String.append("Tuple{", s))
$$ bend % --seq
Tuple{653, 4}
exit 0
$$ bend % --par
Tuple{653, 4}
exit 0
$$ bend % --js
Tuple{653, 4}
exit 0
