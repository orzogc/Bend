# non-zero literal patterns
# ported from bend3: the U32 switch becomes Nat literal patterns
import Base

assert f:
  forall k: Nat
  U32

def f(k):
  match k:
    case 0n:
      10
    case 1n:
      20
    case 5n:
      50
    case k2:
      U32.from_nat(k2)

assert main.out:
  U32

def main.out():
  U32.add(f(0n), U32.add(f(1n), U32.add(f(5n), f(7n))))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
87
$$ bend % --seq
87
exit 0
$$ bend % --par
87
exit 0
$$ bend % --js
87
exit 0
