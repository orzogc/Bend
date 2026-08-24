# bend3's width-8 left-nested chain pinned the Op2 infer arm
# near-linear by interaction count; bend4 has no --stats, so the value
# half carries: the chain checks and answers on every lane
import Base

assert f:
  forall x0: U32
  forall x1: U32
  forall x2: U32
  forall x3: U32
  forall x4: U32
  forall x5: U32
  forall x6: U32
  forall x7: U32
  U32

def f(x0, x1, x2, x3, x4, x5, x6, x7):
  (((((((x0 + x1) + x2) + x3) + x4) + x5) + x6) + x7)

assert main.out:
  Nat

def main.out():
  U32.to_nat(f(0, 1, 2, 3, 4, 5, 6, 7))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
28n
$$ bend % --seq
28n
exit 0
$$ bend % --par
28n
exit 0
$$ bend % --js
28n
exit 0
