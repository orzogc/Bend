# bend3 joined dependent hypotheses into the motive's suffix so both
# retyped per arm; bend4's computed match abstracts nothing -- the arm
# that NEEDS the specialization refuses with the frozen goal, and that
# refusal is the design's own pin (the freeze twins hold the accepted
# half)
import Base

assert j9:
  forall n: Bool
  forall e: {Bool.not(n) == False{} : Bool}
  {n == True{} : Bool}

def j9(n, e):
  match Bool.not(n):
    case False{}:
      {==}
    case True{}:
      {==}

assert main:
  Nat

def main():
  0n
$$ bend %
Error:
- expected : n
- observed : True{}
Context:
- n : Bool
- e : {Bool.not(n) == False{} : Bool}
Location: j9
15 |     case False{}:
16>|       {==}
17 |     case True{}:
