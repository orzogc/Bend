# bend3's Data-ness reached through a TUPLE-returning type family: a
# P2(U32) contracted freely by the sigma table's join. bend4 keeps the
# family transparent -- P2(U32) whnfs to U32 & U32 and destructures --
# and the over-use of a component rides + P2(U32) ~ Pair.copy, whose
# witness types only BECAUSE the family unfolds to U32 & U32, strict;
# the + scrutinee's fields bind Many.
# ported from bend3: (a + b) + a spends a twice, so p binds +
import Base

assert P2:
  forall A: Type
  Type

def P2(A): A & A

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

assert use:
  forall +p: (+ P2(U32) ~ Pair.copy(U32.copy, U32.copy))
  U32

def use(p):
  (a, b) = p
  (a + b) + a

assert main.out:
  U32

def main.out(): use((3, 4))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
10
$$ bend % --seq
10
exit 0
$$ bend % --par
10
exit 0
$$ bend % --js
10
exit 0
