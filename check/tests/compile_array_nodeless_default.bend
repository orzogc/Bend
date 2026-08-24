# boxed-element array of nullary-heavy ctors: swaps move owned values in
# and out (bend3 pinned its nodeless-default refc elision; the moves are
# the dialect-neutral part)
# ported from bend3: the [:Slot] literal becomes an explicit 4-leaf tree
import Base

type Vl:
  MkVl{n: U32}

type Slot:
  Emp{}
  Sub{v: Vl}

assert slot_num:
  forall s: Slot
  U32

def slot_num(s):
  match s:
    case Emp{}:
      0
    case Sub{MkVl{n}}:
      n

assert go:
  forall e: Array<Slot>
  U32

def go(e):
  (e1, a) = Array.swap(Slot, e, 0, Sub{MkVl{7}})
  (e2, b) = Array.swap(Slot, e1, 0, Emp{})
  U32.add(U32.mul(100, slot_num(a)), slot_num(b))

assert main.out:
  U32

def main.out():
  go(ANode{ANode{ALeaf{Emp{}}, ALeaf{Emp{}}}, ANode{ALeaf{Emp{}}, ALeaf{Emp{}}}})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
7
$$ bend % --seq
7
exit 0
$$ bend % --par
7
exit 0
$$ bend % --js
7
exit 0
