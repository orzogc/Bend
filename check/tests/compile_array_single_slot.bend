# Lone-element array of a boxed ctor: swap is the only op, old values
# move out whole
# ported from bend3: the 1-slot [:P] literal becomes a bare ALeaf
import Base

type Pr:
  MkPr{a: U32, b: U32}
  Ep{}

assert pairsum:
  forall p: Pr
  U32

def pairsum(p):
  match p:
    case MkPr{a, b}:
      U32.add(a, b)
    case Ep{}:
      0

assert swp:
  forall a: Array<Pr>
  U32

def swp(a):
  (a2, old) = Array.swap(Pr, a, 0, MkPr{8, 9})
  (a3, old2) = Array.swap(Pr, a2, 0, MkPr{1, 1})
  U32.add(pairsum(old), pairsum(old2))

assert main.out:
  U32

def main.out():
  swp(ALeaf{MkPr{2, 3}})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
22
$$ bend % --seq
22
exit 0
$$ bend % --par
22
exit 0
$$ bend % --js
22
exit 0
