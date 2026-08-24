# bend3 pinned that minted binders print as valid source names; bend4's
# flattener mints them at nested patterns and the --show lane renders
# them (_6 here), a name the parser takes back
import Base

assert pick:
  forall n: Nat
  Nat

def pick(n):
  match n:
    case Succ{Succ{x}}:
      2n
    case n:
      0n

assert main:
  Nat

def main():
  pick(3n)
$$ bend % --show pick
pick = \{Succ: \{Succ: (x => 2n); (_4 => 0n)}; (n => 0n)}
$$ bend %
2n

