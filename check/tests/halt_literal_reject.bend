# descent at literal patterns, reject side: a self-call at a LARGER
# closed literal than the matched one is not a descent (7n is a strict
# superterm of the 5n column, not a subterm).
# ported from bend3: the U32 phase word becomes Nat literals
import Base

assert f:
  forall n: Nat
  Nat

def f(n):
  match n:
    case 5n:
      f(7n)
    case p:
      0n

assert main:
  Nat

def main(): f(3n)
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : f(7n)
Location: f
13 |     case 5n:
14>|       f(7n)
15 |     case p:
