# fork values are free terms: literals, operator chains and calls all
# fork -- ported from bend3 (its fork values were similarly free)
import Base

assert main.out:
  U32

def main.out():
  & a : U32 = 5 & b : U32 = 2 + 3 * 4 & c : U32 = U32.add(1, 1);
  a * 100 + b * 10 + c

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
642
$$ bend % --seq
642
exit 0
$$ bend % --par
642
exit 0
$$ bend % --js
642
exit 0
