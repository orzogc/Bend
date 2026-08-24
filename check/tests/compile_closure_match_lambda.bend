# a bare match lambda passed as a closure value
# ported from bend3: the U32 switch becomes a Nat lambda-match (arm on
# Zero, catch-all tail on the whole value)
import Base

assert run:
  (Nat -> U32) -> U32

def run():
  f => f(3n)

assert main.out:
  U32

def main.out():
  run(\{Zero: 9; n => U32.add(U32.from_nat(n), 100)})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
103
$$ bend % --seq
103
exit 0
$$ bend % --par
103
exit 0
$$ bend % --js
103
exit 0
