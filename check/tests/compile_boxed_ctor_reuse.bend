# 2-u32-field ctor (boxed) built by a closure; the word feeds two uses
# ported from bend3: the contraction becomes a +param helper aliased at
# the matching @+ type (a U32.copy spelling refuses in tocl: structural
# view of a machine word)
import Base

type Point:
  MkPt{x: U32, y: U32}

assert mk.go:
  forall +n: +U32
  Point

def mk.go(n):
  MkPt{n, U32.mul(n, 2)}

assert mk:
  @+n: +U32 -> Point

def mk():
  mk.go

assert get:
  forall p: Point
  U32

def get(p):
  match p:
    case MkPt{x, y}:
      U32.add(x, y)

assert main.out:
  U32

def main.out():
  get(mk(5))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
15
$$ bend % --seq
15
exit 0
$$ bend % --par
15
exit 0
$$ bend % --js
15
exit 0
