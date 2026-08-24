# audit 013 ported: bend3's numeric patterns compiled to numeric
# switches; bend4 has no switch -- a literal pattern desugars to the
# structural U32 ctor chain and flattens like any ctor column, so the
# 0-vs-catch-all match carries over and answers on every lane
import Base

assert f:
  forall n: U32
  Nat

def f(n):
  match n:
    case 0:
      1n
    case n:
      2n

assert main.out:
  Nat

def main.out():
  f(0)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
1n
$$ bend % --js
1n
exit 0
