# an eta-short arm (the def returns a function) whose leaf holds a
# plain let and tails the self-recursive call: the saturating
# application must commute through the statement
# ported from bend3: the counter walks a Nat, its U32 image rebuilt
import Base

assert go:
  forall +f: +Nat
  forall acc: U32
  U32 -> U32

def go(f, acc):
  match f:
    case 0n:
      x => U32.add(x, acc)
    case 1n+g:
      a = U32.add(acc, U32.add(1, U32.from_nat(g)))
      go(g, a)

assert main.out:
  U32

def main.out():
  go(3n, 0)(10)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
16
$$ bend % --seq
16
exit 0
$$ bend % --par
16
exit 0
$$ bend % --js
16
exit 0
