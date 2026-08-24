# io pin (io_reuse_across_effect): bend3 pinned "a lambda owns what it
# captures" across an escaping IO continuation -- a value read again
# in a LATER do-statement lives inside a closure the driver runs after
# the minting body returned. bend4's IO surface exists (IO.print is a
# foreign def), so the block checks -- and dies on the affine wall:
# t and xs are plain binders read by two do-statements, and the usage
# cap never switches off. The pure builders port faithfully: depth
# rides +Nat, the doubled reads ride Cop-licensed + binders, strict.
import Base

type Tree:
  Leaf{v: U32}
  Node{l: Tree, r: Tree}

assert build:
  forall +d: +Nat
  forall +x: +U32
  Tree

def build(d, x):
  match d:
    case 0n:
      Leaf{x}
    case 1n+e:
      Node{build(e, x + x), build(e, x + x + 1)}

assert tsum:
  forall t: Tree
  U32

def tsum(t):
  match t:
    case Leaf{v}:
      v
    case Node{l, r}:
      tsum(l) + tsum(r)

assert lsum:
  forall xs: List<U32>
  U32

def lsum(xs):
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h + lsum(t)

assert main:
  IO(Unit)

def main():
  t = build(3n, 1)
  xs = {[1, 2, 3] : List<U32>}
  do IO<Unit>:
    a : Unit <- IO.print(U32.show(tsum(t)))
    b : Unit <- IO.print(U32.show(tsum(t)))
    c : Unit <- IO.print(U32.show(lsum(xs)))
    d : Unit <- IO.print(U32.show(lsum(xs)))
    return Unit{}
$$ bend %
Error:
- expected : xs
- observed : xs (consumed more than once)
Context:
- t : Tree
Location: main
53 |   t = build(3n, 1)
54>|   xs = {[1, 2, 3] : List<U32>}
55 |   do IO<Unit>:
