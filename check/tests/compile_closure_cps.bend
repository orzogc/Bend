# CPS-style recursion with capturing lambdas
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

assert main.out:
  U32

def main.out():
  go(10n, x => x)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
55
$$ bend % --seq
55
exit 0
$$ bend % --par
55
exit 0
$$ bend % --js
55
exit 0
