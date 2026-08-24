# regression witness (cce7c6b): Array.copy answers its PAIR -- a
# template index shift once turned the second half into the immediate
# word zero (Tuple{kept, 0}, silent). Both halves are swap-probed.
import Base

assert rd:
  forall a: Array<U32>
  U32

def rd(a):
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      U32.add(rd(xs), rd(ys))

assert mk:
  Array<U32>

def mk():
  ANode{ANode{ALeaf{1}, ALeaf{2}}, ANode{ALeaf{3}, ALeaf{4}}}

assert main.out:
  U32

def main.out():
  (x, y) = Array.copy(mk())
  (x2, xo) = Array.swap(U32, x, 1, 9)
  (y2, yo) = Array.swap(U32, y, 2, 7)
  U32.add(rd(x2), U32.add(rd(y2), U32.add(xo, yo)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
36
$$ bend % --seq
36
exit 0
$$ bend % --par
36
exit 0
$$ bend % --js
36
exit 0
