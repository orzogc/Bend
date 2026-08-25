# Nat.div(n, 2n) is not a structural subterm of n: the loop terminates
# at runtime, but the descent judgment refuses it (bend4 has no opt-out, so the
# runnable half of the bend3 test has no place in this file).
# ported from bend3: U32 halving becomes Nat.div
import Base

assert Nat.div:
  forall a: Nat
  forall b: Nat
  Nat

def Nat.div(a, b):
  match Nat.divmod(a, b):
    case (q, r):
      q

assert fold:
  forall n: Nat
  Nat

def fold(n):
  match n:
    case 0n:
      0n
    case n:
      1n+ fold(Nat.div(n, 2n))

assert main:
  Nat

def main(): fold(10n)
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : fold(Nat.div(n, 2n))
Context:
- n : Nat<> - Zero{}
Location: fold
25 |     case n:
26>|       1n+ fold(Nat.div(n, 2n))
27 |
