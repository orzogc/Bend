# audit: type-level self recursion is rejected before conversion can
# loop -- a def body checks live even at Type, so the bare self
# -reference is refused as an escaping value.
# ported from bend3: U32 becomes Nat
import Base

assert a:
  Type

def a(): a
assert main:
  Nat

def main(): 0n
$$ bend %
Error:
- expected : a whole, decreasing self-call (a live self-reference cannot escape as a value)
- observed : a
Location: a
 9 | 
10>| def a(): a
11 | assert main:
