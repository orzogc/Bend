# regression witness (266a45e): a nested Array reaches its consumers
# whole in a KEEP-FREE program -- the cow that unwraps the runtime's
# per-cell seals was once gated on a program-level keep, so block ops
# on an inner array ran on the redirect cell as if it were the block.
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

assert rdd:
  forall n: Array<Array<U32>>
  U32

def rdd(n):
  match n:
    case ALeaf{inner}:
      rd(inner)
    case ANode{xs, ys}:
      U32.add(rdd(xs), rdd(ys))

assert mk2:
  Array<Array<U32>>

def mk2():
  ANode{ALeaf{ANode{ALeaf{10}, ALeaf{20}}}, ALeaf{ANode{ALeaf{30}, ALeaf{2}}}}

assert main.out:
  U32

def main.out():
  (rest, got) = Array.swap(Array<U32>, mk2(), 1, ANode{ALeaf{5}, ALeaf{6}})
  U32.add(rdd(rest), U32.add(rd(got), rdd(mk2())))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
135
$$ bend % --seq
135
exit 0
$$ bend % --par
135
exit 0
$$ bend % --js
135
exit 0
