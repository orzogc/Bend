# the fork-let: & x: A = v & y: B = w; body -- typed bindings pairing
# into Par/Both at parse time, three-wide here (right-nested pairs, so
# no arity cap, bend3's dead-cap law carried). ported from bend3: the
# bindings spell their types (no inference) and the values are calls
import Base

assert f:
  forall n: U32
  U32

def f(n):
  n * 3

assert main.out:
  U32

def main.out():
  & a : U32 = f(1) & b : U32 = f(2) & c : U32 = f(3);
  a + b + c

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
18
$$ bend % --seq
18
exit 0
$$ bend % --par
18
exit 0
$$ bend % --js
18
exit 0
