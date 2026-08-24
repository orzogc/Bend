# bend3's {a != b} desugar minted an Empty.Not def, so a user def of
# that name collided; bend4's != unfolds structurally at parse time --
# no mint, no collision: a user Empty.Not coexists with the sugar
import Base

assert Empty.Not:
  forall -A: Type
  Type

def Empty.Not(A):
  A -> Empty

assert NEQ:
  Type

def NEQ():
  {1n != 2n : Nat}

assert main:
  Nat

def main():
  3n
$$ bend %
3n
