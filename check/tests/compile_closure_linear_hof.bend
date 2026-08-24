# a HOF taking a linear closure
# ported from bend3 (a + b -> U32.add)
import Base

assert run:
  (U32 -> U32) -> U32 -> U32

def run():
  f => x => f(x)

assert plus:
  U32 -> U32 -> U32

def plus():
  a => b => U32.add(a, b)

assert main.out:
  U32

def main.out():
  run(plus(40), 2)

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
