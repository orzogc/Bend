# bend3's capture-position hoist (an under-applied call's argument
# minting apply$ in a pure leaf); bend4 has no taint hoist and
# under-applied defs are plain values -- the partial applications bind,
# apply later, and the value carries: 28
import Base

type Pr8:
  Pr8{x: U32, y: U32}

assert add3:
  forall a: U32
  forall b: U32
  forall c: U32
  U32

def add3(a, b, c):
  (a + b) + c

assert sum8:
  forall p: Pr8
  U32

def sum8(p):
  match p:
    case Pr8{x, y}:
      x + y

assert main.out:
  Nat

def main.out():
  g = {y => y + 1 : U32 -> U32}
  h = {add3(g(2)) : U32 -> U32 -> U32}
  k = {add3(sum8(Pr8{7, 8})) : U32 -> U32 -> U32}
  U32.to_nat(h(3, 4) + k(1, 2))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
28n
$$ bend % --seq
28n
exit 0
$$ bend % --par
28n
exit 0
$$ bend % --js
28n
exit 0
