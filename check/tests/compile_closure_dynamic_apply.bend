# two-arg dynamic application + closure picked by a branch
# ported from bend3: the U32 branch becomes a Bool match
import Base

assert pick:
  forall n: Bool
  U32 -> U32 -> U32

def pick(n):
  match n:
    case True{}:
      a => b => U32.add(a, b)
    case False{}:
      a => b => U32.mul(a, b)

assert use:
  (U32 -> U32 -> U32) -> U32

def use():
  f => f(3, 4)

assert main.out:
  U32

def main.out():
  U32.add(use(pick(True{})), use(pick(False{})))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
19
$$ bend % --seq
19
exit 0
$$ bend % --par
19
exit 0
$$ bend % --js
19
exit 0
