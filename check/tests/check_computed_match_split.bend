# bend3's one-split pin: `match isz(n):` abstracted the call into the
# motive and the proof closed per arm. bend4's computed match never
# specializes the goal, by design -- the same spelling refuses, and
# that refusal is the pin (the frozen spelling is pinned positively by
# page_arm_leaf_context)
import Base

assert isz:
  forall n: Nat
  Bool

def isz(n):
  match n:
    case Zero{}:
      True{}
    case Succ{p}:
      False{}

assert orb:
  forall a: Bool
  forall b: Bool
  Bool

def orb(a, b):
  match a:
    case True{}:
      True{}
    case False{}:
      b

assert or_true:
  forall n: Nat
  {orb(isz(n), True{}) == True{} : Bool}

def or_true(n):
  match isz(n):
    case True{}:
      {==}
    case False{}:
      {==}

assert main:
  Nat

def main():
  0n
$$ bend %
Error:
- expected : orb(isz(n), True{})
- observed : True{}
Context:
- n : Nat
Location: or_true
37 |     case True{}:
38>|       {==}
39 |     case False{}:
