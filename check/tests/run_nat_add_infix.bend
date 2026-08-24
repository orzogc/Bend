# SPEC PART 3: infix +n is Nat.add at the additive level -- a chain
# folds left, 1n +n 2n +n 3n answers 6n on every lane
import Base

assert main.out:
  Nat

def main.out():
  1n +n 2n +n 3n

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
6n
$$ bend % --seq
6n
exit 0
$$ bend % --par
6n
exit 0
$$ bend % --js
6n
exit 0
