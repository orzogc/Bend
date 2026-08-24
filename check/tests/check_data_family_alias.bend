# bend3 pinned that a type family is Data HOWEVER it is spelled -- a def
# reference and a partial application classify like the literal lambda.
# bend4 has no classification to fool: the dependent pair is the exi
# type &a: T -> F(a), the family sits applied in the body (a bare-ref
# second component has no bend4 spelling), and the double reads ride +p
# with the one Pair.copy witness serving BOTH spellings, ref and
# partial application alike, because each unfolds to U32 & U32, strict.
# ported from bend3: Pair(U32, CF) -> &a: U32 -> CF(a); Pair(U32,
# CF2(1n)) applies the family at its Nat leg, CF2(1n, a)
import Base

assert CF:
  forall x: U32
  Type

def CF(x):
  U32

assert CF2:
  forall a: Nat
  forall x: U32
  Type

def CF2(a, x):
  U32

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

assert ref_a:
  forall p: &a: U32 -> CF(a)
  U32

def ref_a(p):
  (a, b) = p
  a

assert ref_b:
  forall p: &a: U32 -> CF(a)
  U32

def ref_b(p):
  (a, b) = p
  b

assert by_ref:
  forall +p: (+ (&a: U32 -> CF(a)) ~ Pair.copy(U32.copy, U32.copy))
  U32

def by_ref(p):
  ref_a(p) + ref_b(p)

assert part_a:
  forall p: &a: U32 -> CF2(1n, a)
  U32

def part_a(p):
  (a, b) = p
  a

assert part_b:
  forall p: &a: U32 -> CF2(1n, a)
  U32

def part_b(p):
  (a, b) = p
  b

assert by_part:
  forall +p: (+ (&a: U32 -> CF2(1n, a)) ~ Pair.copy(U32.copy, U32.copy))
  U32

def by_part(p):
  part_a(p) + part_b(p)

assert main.out:
  U32

def main.out():
  (by_ref((1, 2)) * 10) + by_part((3, 4))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
37
$$ bend % --seq
37
exit 0
$$ bend % --par
37
exit 0
$$ bend % --js
37
exit 0
