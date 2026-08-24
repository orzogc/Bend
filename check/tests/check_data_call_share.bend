# bend3's Data-kinded dup planted a deep copy BY VALUE: a call in the
# duplicated position (dbl(3)) ran once and its value copied. bend4's
# copy is the Cop-licensed + binder and is by value the same way:
# dup3's +x lands in MkPr4{x, x} and both copies read 6, so the
# flattened readback doubles; the local Pr3.copy witness licenses it,
# strict. dbl's own x + x re-spend rides +U32.
# ported from bend3: the @-a: Data polymorphic dup is monomorphized
# (no Data kind); the printed-pair golden becomes the flattened sum
import Base

type Pr3:
  MkPr3{x: U32, y: U32}
type Pr4:
  MkPr4{a: Pr3, b: Pr3}

assert Pr3.copy:
  forall p: Pr3
  Copy(Pr3, p) & Copy(Pr3, p)

def Pr3.copy(p):
  match p:
    case MkPr3{x, y}:
      ((xx, xe), (xy, xf)) = U32.copy(x)
      ((yx, ye), (yy, yf)) = U32.copy(y)
      s10 = Equal.cong(U32, Pr3, z => MkPr3{z, y}, x, xx, xe)
      s11 = Equal.cong(U32, Pr3, z => MkPr3{xx, z}, y, yx, ye)
      t11 = Equal.trans(Pr3, MkPr3{x, y}, MkPr3{xx, y}, MkPr3{xx, yx}, s10, s11)
      s20 = Equal.cong(U32, Pr3, z => MkPr3{z, y}, x, xy, xf)
      s21 = Equal.cong(U32, Pr3, z => MkPr3{xy, z}, y, yy, yf)
      t21 = Equal.trans(Pr3, MkPr3{x, y}, MkPr3{xy, y}, MkPr3{xy, yy}, s20, s21)
      ((MkPr3{xx, yx}, t11), (MkPr3{xy, yy}, t21))

assert dbl:
  forall +x: +U32
  U32

def dbl(x):
  x + x

assert dup3:
  forall +x: +Pr3
  Pr4

def dup3(x):
  MkPr4{x, x}

assert flat.go:
  forall p: Pr3
  U32

def flat.go(p):
  match p:
    case MkPr3{x, y}:
      (10 * x) + y

assert flat:
  forall q: Pr4
  U32

def flat(q):
  match q:
    case MkPr4{a, b}:
      flat.go(a) + flat.go(b)

assert main.out:
  U32

def main.out():
  flat(dup3(MkPr3{dbl(3), 4}))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
128
$$ bend % --seq
128
exit 0
$$ bend % --par
128
exit 0
$$ bend % --js
128
exit 0
