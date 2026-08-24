# the second ordinary program: floats and an Array<F32> beside Map,
# Set, number-text and a KEPT tuple binder, all in ONE book - crossing
# the whole-book representation seams (shared Tup, F32 array cells)
# where the merged-book defects lived (reg_share_tuple_global, the
# map_set_ops shard divergence); no interp lane (F32 axioms stuck there)
import Base

assert Pair.copy:
  forall -c1: Copiable(U32)
  forall -c2: Copiable(U32)
  forall t: U32 & U32
  Copy(U32 & U32, t) & Copy(U32 & U32, t)

def Pair.copy(c1, c2, t):
  (a, b) = t
  ((ax, ae), (ay, af)) = U32.copy(a)
  ((bx, be), (by, bf)) = U32.copy(b)
  s10 = Equal.cong(U32, U32 & U32, z => (z, b), a, ax, ae)
  s11 = Equal.cong(U32, U32 & U32, z => (ax, z), b, bx, be)
  t11 = Equal.trans(U32 & U32, (a, b), (ax, b), (ax, bx), s10, s11)
  s20 = Equal.cong(U32, U32 & U32, z => (z, b), a, ay, af)
  s21 = Equal.cong(U32, U32 & U32, z => (ay, z), b, by, bf)
  t21 = Equal.trans(U32 & U32, (a, b), (ay, b), (ay, by), s20, s21)
  (((ax, bx), t11), ((ay, by), t21))

assert u32cp:
  forall v: U32
  (U32 & U32)

def u32cp(v):
  ((a, e1), (b, e2)) = U32.copy(v)
  (a, b)

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert pa:
  forall q: (U32 & U32)
  U32

def pa(q):
  (a, b) = q
  a

assert pb:
  forall q: (U32 & U32)
  U32

def pb(q):
  (a, b) = q
  b

assert keep2:
  forall +p: (+ (U32 & U32) ~ Pair.copy(U32.copy, U32.copy))
  U32

def keep2(p):
  pa(p) + pb(p)

assert rdu:
  forall s: String
  U32

def rdu(s):
  match U32.read(s):
    case Some{v}:
      v
    case None{}:
      999

assert rdn:
  forall s: String
  Nat

def rdn(s):
  match Nat.read(s):
    case Some{v}:
      v
    case None{}:
      0n

assert fpart:
  U32

def fpart():
  m = {ANode{ALeaf{0.5}, ALeaf{1.5}} : Array<F32>};
  (m2, v0) = Array.swap(F32, m, 0, 2.0)
  (m3, v1) = Array.swap(F32, m2, 1, 0.25)
  F32.to_u32((v0 +. v1) *. (6.25 -. 2.25))

assert main.out:
  U32

def main.out():
  s1 = Set.add(Set.add(Set.new(), U32.show(12)), Nat.show(3n));
  (s2, h12) = Set.has(s1, "12")
  m = Map.set(U32, Map.new(U32), "k" ++ U32.show(7), 70);
  (m2, v) = Map.get(U32, u32cp, 0, m, "k7")
  c0 = b2u(h12)
  c1 = b2u(U32.is_eq(v, 70))
  c2 = b2u(U32.is_eq(rdu("29") + U32.from_nat(rdn("13")), 42))
  c3 = b2u(U32.is_eq(keep2((3, 4)), 7))
  fpart() * 10000 + c0 * 1000 + c1 * 100 + c2 * 10 + c3

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
81111
exit 0
$$ bend % --par
81111
exit 0
$$ bend % --js
81111
exit 0
