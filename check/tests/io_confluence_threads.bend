# CONFLUENCE under real threads: a 4096-leaf fork tree of
# wrap-arithmetic leaves gives the SAME U32 checksum at one thread and
# at eight -- 506569506, bend3's own golden (verified against an
# independent host-JS mirror). No interp lane: the structural Word
# evaluator needs minutes for 4096 hash leaves, so the pin is one
# thread v eight v the JS oracle.
# ported from bend3: depth becomes Nat fuel, forks spell the Par<>
# Both destructure, operators spell U32.xor/shln/shrn/mul/add, reused
# words take +U32 Cop binders
import Base

assert leaf:
  forall +i: +U32
  U32

def leaf(i):
  +x = {U32.mul(U32.xor(i, U32.shln(13n, i)), 2654435761) : +U32}
  U32.add(U32.xor(x, U32.shrn(17n, x)), i)

assert tree:
  forall +d: +Nat
  forall +i: +U32
  U32

def tree(d, i):
  match d:
    case 0n:
      leaf(i)
    case 1n+e:
      Both{a, b} = {Both{tree(e, U32.mul(i, 2)), tree(e, U32.add(U32.mul(i, 2), 1))} : Par<U32, U32>}
      U32.add(a, b)

assert main.out:
  U32

def main.out():
  tree(12n, 1)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
506569506
exit 0
$$ bend % --par
506569506
exit 0
$$ bend % --js
506569506
exit 0
