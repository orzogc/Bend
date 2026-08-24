# default rebind then deeper columns re-matched
# ported from bend3: local Nat-like type with bare ctor names
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

assert g:
  forall a: Nt
  forall b: Nt
  U32

def g(a, b):
  match a, b:
    case Zr{}, Zr{}:
      1
    case x, Zr{}:
      2
    case Zr{}, Sc{y}:
      3
    case x, Sc{y}:
      4

assert main.out:
  U32

def main.out():
  U32.add(g(Zr{}, Zr{}), U32.add(g(Sc{Zr{}}, Zr{}), U32.add(g(Zr{}, Sc{Zr{}}), g(Sc{Zr{}}, Sc{Zr{}}))))

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
