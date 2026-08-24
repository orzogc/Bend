# bare Ref value: a zero-arg def used as a value argument
# ported from bend3 (x * 2 -> U32.mul)
import Base

assert seed:
  U32

def seed():
  42

assert double:
  U32 -> U32

def double():
  x => U32.mul(x, 2)

assert main.out:
  U32

def main.out():
  double(seed)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
84
$$ bend % --seq
84
exit 0
$$ bend % --par
84
exit 0
$$ bend % --js
84
exit 0
