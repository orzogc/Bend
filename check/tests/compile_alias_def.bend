# alias def: body is a bare Ref; ported from bend3 (x * 3 -> U32.mul)
import Base

assert g:
  U32 -> U32

def g():
  x => U32.mul(x, 3)

assert f:
  U32 -> U32

def f():
  g

assert main.out:
  U32

def main.out():
  f(7)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
21
$$ bend % --seq
21
exit 0
$$ bend % --par
21
exit 0
$$ bend % --js
21
exit 0
