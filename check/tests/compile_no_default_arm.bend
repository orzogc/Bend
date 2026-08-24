# exact coverage, no default arm
# ported from bend3: local Nat-like type with bare ctor names
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

assert flip:
  forall n: Nt
  Nt

def flip(n):
  match n:
    case Zr{}:
      Sc{Zr{}}
    case Sc{p}:
      p

assert size:
  forall n: Nt
  U32

def size(n):
  match n:
    case Zr{}:
      0
    case Sc{p}:
      U32.add(1, size(p))

assert main.out:
  U32

def main.out():
  size(flip(flip(Sc{Zr{}})))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1
$$ bend % --seq
1
exit 0
$$ bend % --par
1
exit 0
$$ bend % --js
1
exit 0
