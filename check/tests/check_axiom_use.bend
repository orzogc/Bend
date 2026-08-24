# an axiom (bodiless assert) is a DEAD claim: a live rewrite cannot run
# on it, so the fill below is refused at the evidence.
# ported from bend3: bend3 admitted axioms in later proofs with a
# warning; bend4 pins the refusal (rewrite evidence is live)
import Base

assert plus_comm:
  forall a : U32
  forall b : U32
  {U32.add(a, b) == U32.add(b, a) : U32}

assert shift:
  forall a: U32
  forall b: U32
  {U32.add(U32.add(a, b), 0) == U32.add(U32.add(b, a), 0) : U32}

def shift(a, b):
  %h@plus_comm(a, b) : {U32.add(_, 0) == U32.add(U32.add(b, a), 0) : U32}; {==}

assert main:
  U32

def main(): 0
$$ bend %
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : plus_comm
Context:
- a : U32
- b : U32
Location: shift
17 | def shift(a, b):
18>|   %h@plus_comm(a, b) : {U32.add(_, 0) == U32.add(U32.add(b, a), 0) : U32}; {==}
19 |
