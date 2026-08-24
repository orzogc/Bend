# match default arm that rebinds and rebuilds
# ported from bend3: local Nat-like type with bare ctor names
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

assert peel:
  forall a: Nt
  forall b: Nt
  Nt

def peel(a, b):
  match a, b:
    case Sc{x}, Sc{y}:
      x
    case Zr{}, y:
      y
    case x, y:
      x

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
  U32.add(size(peel(Sc{Sc{Zr{}}}, Sc{Zr{}})), size(peel(Sc{Zr{}}, Zr{})))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2
$$ bend % --seq
2
exit 0
$$ bend % --par
2
exit 0
$$ bend % --js
2
exit 0
