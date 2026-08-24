# descent with threaded state: the growing accumulator rides free
# AFTER the decreasing column -- col0 shrinks, so col1 is never
# compared. (Before the decreasing column it would sit at col0, break
# the left-to-right EQ chain, and be refused: bend3's found-column
# search is gone.)
# ported from bend3: the counter becomes Nat, the U32 accumulator
# rides U32.add, the answer reads back through U32.to_nat
import Base

assert go:
  forall n: Nat
  forall acc: U32
  Nat

def go(n, acc):
  match n:
    case 0n:
      U32.to_nat(acc)
    case 1n+p:
      go(p, U32.add(acc, 1))

assert main.out:
  Nat

def main.out(): go(3n, 10)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
13n
$$ bend % --seq
13n
exit 0
$$ bend % --par
13n
exit 0
$$ bend % --js
13n
exit 0
