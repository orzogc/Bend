# forks nest: a fork binding's body may fork again, and a fork value
# may itself be a call whose argument forked -- ported from bend3's
# second arity shape
import Base

assert w:
  forall n: U32
  U32

def w(n):
  n + 1

assert inner:
  forall x: U32
  U32

def inner(x):
  & p : U32 = w(x) & q : U32 = w(10);
  p + q

assert main.out:
  U32

def main.out():
  & a : U32 = inner(1) & b : U32 = inner(2);
  a * 100 + b

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
1314
$$ bend % --seq
1314
exit 0
$$ bend % --par
1314
exit 0
$$ bend % --js
1314
exit 0
