# bend3's interp cost guard for a linear 16-cons fold loses its counter
# (no --stats in bend4) and keeps its value: build's 1+n arm becomes a
# Nat countdown with a U32 mirror, fold carries over verbatim
import Base

type L:
  LC{h: U32, t: L}
  LN{}

assert build:
  forall n: Nat
  forall i: U32
  L

def build(n, i):
  match n:
    case Zero{}:
      LN{}
    case Succ{k}:
      ((i1, d1), (i2, d2)) = U32.copy(i)
      LC{i1, build(k, i2 - 1)}

assert fold:
  forall xs: L
  forall acc: U32
  U32

def fold(xs, acc):
  match xs:
    case LN{}:
      acc
    case LC{h, t}:
      fold(t, acc + h)

assert main.out:
  Nat

def main.out():
  U32.to_nat(fold(build(16n, 16), 0))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
136n
$$ bend % --seq
136n
exit 0
$$ bend % --par
136n
exit 0
$$ bend % --js
136n
exit 0
