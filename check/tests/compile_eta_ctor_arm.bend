# eta-short ctor arm: the Sc arm of a lambda-match is a bare Ref
# consuming the field
# ported from bend3: local Nat-like type with bare ctor names
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

assert size:
  forall n: Nt
  U32

def size(n):
  match n:
    case Zr{}:
      0
    case Sc{p}:
      U32.add(1, size(p))

assert f:
  Nt -> U32

def f():
  \{Zr: 99; Sc: size}

assert main.out:
  U32

def main.out():
  U32.add(f(Zr{}), f(Sc{Sc{Zr{}}}))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
100
$$ bend % --seq
100
exit 0
$$ bend % --par
100
exit 0
$$ bend % --js
100
exit 0
