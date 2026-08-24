# free word contraction feeding a recursive tail call: the element is
# both passed on and stored in the ctor
# ported from bend3: the counter walks a Nat, the doubled word a +param
import Base

type Lst:
  Cn{h: U32, t: Lst}
  Nl{}

assert go:
  forall +f: +Nat
  forall +n: +U32
  forall acc: Lst
  Lst

def go(f, n, acc):
  match f:
    case 0n:
      acc
    case 1n+g:
      go(g, n, Cn{n, acc})

assert main.out:
  U32

def main.out():
  match go(3n, 242, Nl{}):
    case Cn{h, t}:
      h
    case Nl{}:
      0

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
242
$$ bend % --seq
242
exit 0
$$ bend % --par
242
exit 0
$$ bend % --js
242
exit 0
