# an unused higher-order def must be pruned (reachability), not compiled
# ported from bend3 (x * 2 -> U32.mul)
import Base

assert lemma:
  @f: (@x: U32 -> U32) -> U32

def lemma():
  f => f(3)

assert double:
  U32 -> U32

def double():
  x => U32.mul(x, 2)

assert main.out:
  U32

def main.out():
  double(21)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
42
$$ bend % --seq
42
exit 0
$$ bend % --par
42
exit 0
$$ bend % --js
42
exit 0
