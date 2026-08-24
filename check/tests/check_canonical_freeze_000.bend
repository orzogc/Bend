# bend3's freeze law: a canonical computed scrutinee must NOT rewrite
# a coincidental spelling in a hypothesis (the (Z,Z) corner tautology
# corruption); bend4 freezes unconditionally -- computed matches never
# specialize anything, so the arms' goal stays unrewritten and the
# ORIGINAL hypothesis discharges both, the corruption unspellable
import Base

assert f9:
  forall n: Bool
  forall e: {Bool.and(n, False{}) == False{} : Bool}
  {Bool.and(n, False{}) == False{} : Bool}

def f9(n, e):
  match Bool.and(n, False{}):
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
