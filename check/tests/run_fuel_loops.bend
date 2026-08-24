# fuel-bounded loops (the GUIDE's fuel idiom): Euclid's gcd and a Collatz
# step count, both driven by a decreasing first column
# ported from bend3: fuel becomes Nat, U32 sub-matches become nested Bool
# matches, shared words +U32 (Cop) binders
import Base

assert gcd:
  forall fuel: Nat
  forall a: U32
  forall +b: +U32
  U32

def gcd(fuel, a, b):
  match fuel:
    case 0n:
      0
    case 1n+f:
      match U32.is_zero(b):
        case True{}:
          a
        case False{}:
          gcd(f, b, U32.mod(a, b))

assert collatz:
  forall fuel: Nat
  forall +n: +U32
  forall steps: U32
  U32

def collatz(fuel, n, steps):
  match fuel:
    case 0n:
      9999
    case 1n+f:
      match U32.is_eq(n, 1):
        case True{}:
          steps
        case False{}:
          match U32.is_zero(U32.mod(n, 2)):
            case True{}:
              collatz(f, U32.div(n, 2), U32.add(steps, 1))
            case False{}:
              collatz(f, U32.add(U32.mul(3, n), 1), U32.add(steps, 1))

assert main.out:
  U32

def main.out():
  U32.add(U32.mul(gcd(10n, 1071, 462), 1000), collatz(120n, 27, 0))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
21111
$$ bend % --seq
21111
exit 0
$$ bend % --par
21111
exit 0
$$ bend % --js
21111
exit 0
