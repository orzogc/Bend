# audit: direct polymorphic self recursion is rejected before use --
# loop(a) is a whole self-call with no shrinking column, refused even
# though it sits under the type binder a.
# ported from bend3: U32 becomes Nat
import Base

assert loop:
  @a:Type -> a

def loop(): a => loop(a)
assert main:
  Nat

def main(): loop(Nat)
$$ bend %
Error:
- expected : a decreasing self-call (some live argument must shrink)
- observed : loop(a)
Context:
- a : Type
Location: loop
 9 | 
10>| def loop(): a => loop(a)
11 | assert main:
