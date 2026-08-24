# closure/HOF pipelines: compose chains (every closure consumed exactly
# once), a recursively BUILT closure chain, and a closure stored in and
# extracted from a constructor field
# ported from bend3: generics become erased Type params, the chain
# counter becomes Nat with its U32 image rebuilt via U32.from_nat
import Base

assert compose:
  forall -A: Type
  forall -B: Type
  forall -C: Type
  forall f: A -> B
  forall g: B -> C
  A -> C

def compose(A, B, C, f, g):
  x => g(f(x))

type FBox:
  MkF{f: U32 -> U32}

assert chain:
  forall +n: +Nat
  U32 -> U32

def chain(n):
  match n:
    case 0n:
      x => x
    case 1n+p:
      k = U32.add(1, U32.from_nat(p))
      compose(U32, U32, U32, x => U32.add(x, k), chain(p))

assert unbox:
  forall b: FBox
  U32

def unbox(b):
  match b:
    case MkF{f}:
      f(4)

assert sqr:
  forall x: U32
  U32

def sqr(x):
  +y = {x : +U32}
  U32.mul(y, y)

assert main.out:
  U32

def main.out():
  a = (compose(U32, U32, U32, compose(U32, U32, U32, x => U32.add(x, 1), x => U32.mul(x, 2)), sqr))(3)
  b = (chain(3n))(10)
  c = unbox(MkF{y => U32.mul(y, 5)})
  U32.add(U32.add(U32.mul(a, 1000), U32.mul(b, 10)), c)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
64180
$$ bend % --seq
64180
exit 0
$$ bend % --par
64180
exit 0
$$ bend % --js
64180
exit 0
