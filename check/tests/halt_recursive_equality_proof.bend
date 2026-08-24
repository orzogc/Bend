# audit: recursive equality proofs cannot justify casts -- bad is a
# whole self-reference escaping as a value, refused at the def, so its
# claimed {Nat == D : Type} never reaches a rewrite.
# ported from bend3: U32 becomes Nat; the cast site falls with the def
import Base

type D:
  K{}

assert bad:
  {Nat == D : Type}

def bad(): bad
assert main:
  Nat

def main(): 0n
$$ bend %
Error:
- expected : a whole, decreasing self-call (a live self-reference cannot escape as a value)
- observed : bad
Location: bad
12 | 
13>| def bad(): bad
14 | assert main:
