# a capturing closure (partial application) passed into a matching def
# ported from bend3 (a + b -> U32.add)
import Base

type PairU:
  MkPair{a: U32, b: U32}

assert mkadd:
  U32 -> U32 -> U32

def mkadd():
  n => x => U32.add(x, n)

assert fold:
  forall p: PairU
  forall f: U32 -> U32
  U32

def fold(p, f):
  match p:
    case MkPair{a, b}:
      f(U32.add(a, b))

assert main.out:
  U32

def main.out():
  fold(MkPair{3, 4}, mkadd(10))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
17
$$ bend % --seq
17
exit 0
$$ bend % --par
17
exit 0
$$ bend % --js
17
exit 0
