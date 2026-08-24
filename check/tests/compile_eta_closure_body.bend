# eta-short closure body: a def that returns its function arg bare
# ported from bend3 (x * 2 -> U32.mul)
import Base

assert double:
  U32 -> U32

def double():
  x => U32.mul(x, 2)

assert twice:
  (U32 -> U32) -> U32 -> U32

def twice():
  f => x => f(x)

assert comp:
  (U32 -> U32) -> U32 -> U32

def comp():
  f => f

assert main.out:
  U32

def main.out():
  U32.add(twice(double, 10), comp(double, 11))

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
