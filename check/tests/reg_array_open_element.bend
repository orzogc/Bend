# regression witness (2ff58c0): an OPEN Array element type refuses loud
# at emission -- one untyped segment cannot serve two representations,
# so a generic helper over Array<T> is reported, never compiled wrong.
# The evaluator and the JS backend run it fine.
import Base

assert gcount:
  forall -T: Type
  forall a: Array<T>
  U32

def gcount(T, a):
  match a:
    case ALeaf{x}:
      d = x
      1
    case ANode{xs, ys}:
      U32.add(gcount(T, xs), gcount(T, ys))

assert main.out:
  U32

def main.out():
  gcount(U32, ANode{ALeaf{3}, ALeaf{4}})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2
$$ bend % --seq
Error: an open Array element type
exit 1
$$ bend % --js
2
exit 0
