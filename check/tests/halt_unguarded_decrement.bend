# an unguarded decrement is NOT smaller: without a match the argument
# may already be zero (Nat.sub truncates), so f(Nat.sub(d, 1n)) shrinks
# no column and the self-call is refused.
# ported from bend3: the U32 wrap-around argument becomes Nat.sub
import Base

assert f:
  forall d: Nat
  Nat

def f(d):
  f(Nat.sub(d, 1n))

assert main:
  Nat

def main(): 0n
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : f(Nat.sub(d, 1n))
Context:
- d : Nat
Location: f
11 | def f(d):
12>|   f(Nat.sub(d, 1n))
13 |
