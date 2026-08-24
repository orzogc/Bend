# literal pattern nested inside a ctor
# ported from bend3: the U32 field becomes a Nat, the literal a 0n
import Base

type Nt:
  Zr{}
  Sc{p: Nat}

assert f:
  forall n: Nt
  U32

def f(n):
  match n:
    case Zr{}:
      0
    case Sc{0n}:
      100
    case Sc{k}:
      U32.from_nat(k)

assert main.out:
  U32

def main.out():
  U32.add(f(Sc{0n}), U32.add(f(Sc{7n}), f(Zr{})))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
107
$$ bend % --seq
107
exit 0
$$ bend % --par
107
exit 0
$$ bend % --js
107
exit 0
