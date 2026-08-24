# boxed-element array: entries move in and out by swap, defaults included
# (bend3 pinned its static-default storage; the swap semantics is the
# dialect-neutral part)
# ported from bend3: the [:Opt] literal becomes an explicit 4-leaf tree
import Base

type Opt:
  Pt{a: U32, b: U32}
  Nt{}

assert osum:
  forall o: Opt
  U32

def osum(o):
  match o:
    case Pt{a, b}:
      U32.add(a, b)
    case Nt{}:
      100

assert main.out:
  U32

def main.out():
  (a1, x) = Array.swap(Opt, ANode{ANode{ALeaf{Pt{1, 2}}, ALeaf{Nt{}}}, ANode{ALeaf{Pt{5, 6}}, ALeaf{Nt{}}}}, 0, Nt{})
  (a2, y) = Array.swap(Opt, a1, 1, Nt{})
  (a3, z) = Array.swap(Opt, a2, 3, Nt{})
  (a4, w) = Array.swap(Opt, a3, 2, Nt{})
  U32.add(U32.add(osum(x), osum(y)), U32.add(osum(z), osum(w)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
214
$$ bend % --seq
214
exit 0
$$ bend % --par
214
exit 0
$$ bend % --js
214
exit 0
