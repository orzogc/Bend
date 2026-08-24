# two-peel numeric recursion, respelled on Nat's ladder (the ruled
# port of bend3's nested U32 dec-switch): div2n is the test's own
# two-peel eliminator, the mirrored-twin proof closes arm for arm
# against base's Nat.half, and the U32 face carries the runtime.
# ported from bend3: main keeps the golden 5
import Base

assert Nat.half:
  forall m: Nat
  Nat

def Nat.half(m):
  match m:
    case 0n:
      0n
    case 1n:
      0n
    case 2n+r:
      1n+Nat.half(r)

assert div2n:
  forall m: Nat
  Nat

def div2n(m):
  match m:
    case 0n:
      0n
    case 1n:
      0n
    case 2n+q:
      1n+div2n(q)

assert div2n_half:
  forall m: Nat
  {div2n(m) == Nat.half(m) : Nat}

def div2n_half(m):
  match m:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+q:
      Equal.cong(Nat, Nat, y => 1n+y, div2n(q), Nat.half(q), div2n_half(q))

assert div2u:
  forall a: U32
  U32

def div2u(a):
  U32.from_nat(div2n(U32.to_nat(a)))

assert main.out:
  U32

def main.out():
  div2u(11)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
5
$$ bend % --seq
5
exit 0
$$ bend % --par
5
exit 0
$$ bend % --js
5
exit 0
