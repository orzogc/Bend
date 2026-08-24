# bend3's `match a!` computed opt-out mark (ironically named for
# bend4's parser); bend4's own ! is the GPU bang before a call's
# parens and no scrutinee mark exists -- the spelling dies at parse
import Base

assert f:
  forall n: Nat
  Nat

def f(n):
  match n!:
    case Zero{}:
      0n
    case Succ{p}:
      1n

assert main:
  Nat

def main():
  f(2n)
$$ bend %
Error:
- expected : a term
- observed : '!'
Location:
10 | def f(n):
11>|   match n!:
12 |     case Zero{}:
