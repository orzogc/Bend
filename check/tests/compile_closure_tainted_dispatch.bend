# closure literal of a recursive def + dispatch through dynamic apply
# ported from bend3: the counter walks a Nat, its U32 image rebuilt
import Base

assert go:
  forall +n: +Nat
  forall k: U32 -> U32
  U32

def go(n, k):
  match n:
    case 0n:
      k(0)
    case 1n+p:
      go(p, r => k(U32.add(r, U32.add(1, U32.from_nat(p)))))

assert use:
  ((U32 -> U32) -> U32) -> U32

def use():
  f => f(x => U32.add(x, 1000))

assert main.out:
  U32

def main.out():
  use(go(10n))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1055
$$ bend % --seq
1055
exit 0
$$ bend % --par
1055
exit 0
$$ bend % --js
1055
exit 0
