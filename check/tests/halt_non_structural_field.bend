# audit: recursion on a constructor field applied to an argument (g(0n))
# is not a structural subterm and is refused -- this is what blocks the
# impredicative-ordinals / wellfoundedness paradox (bend4 has no
# positivity check; this wall is the guard).
# ported from bend3: bare ctors, U32 becomes Nat
import Base

type Ord:
  Sup{g: Nat -> Ord}

assert rec:
  forall o: Ord
  Unit

def rec(o):
  match o:
    case Sup{g}:
      rec(g(0n))

assert main:
  Nat

def main(): 0n
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : rec(g(0n))
Context:
- g : @_:Nat -> Ord
Location: rec
17 |     case Sup{g}:
18>|       rec(g(0n))
19 |
