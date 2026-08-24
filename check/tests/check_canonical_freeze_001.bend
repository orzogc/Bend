# check_canonical_freeze_000's numeric flavor rode 0/1/2+ switches;
# bend4 has no number switches and the same unconditional freeze --
# the is_eq dispatch's arms keep the frozen goal and the original
# hypothesis closes them
import Base

assert g9:
  forall n: U32
  forall e: {U32.is_eq(n, 0) == True{} : Bool}
  {U32.is_eq(n, 0) == True{} : Bool}

def g9(n, e):
  match U32.is_eq(n, 0):
    case True{}:
      e
    case False{}:
      e

assert main.out:
  Nat

def main.out():
  0n

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
0n
$$ bend % --seq
0n
exit 0
$$ bend % --par
0n
exit 0
$$ bend % --js
0n
exit 0
