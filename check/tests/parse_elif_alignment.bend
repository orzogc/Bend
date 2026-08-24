# bend3 pinned elif alignment against its layout; bend4 is layout-free
# and any indentation reads the same chain
import Base

assert f:
  forall x: U32
  U32

def f(x):
  if U32.is_zero(x): 5
      elif {True{} : Bool}: 6
  else: 7

assert main.out:
  U32

def main.out():
  f(0) * 10 + f(3)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
56
$$ bend % --seq
56
exit 0
$$ bend % --js
56
exit 0
