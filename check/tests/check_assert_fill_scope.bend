# an assert declares a DEAD claim: a def between the assert and its
# fill cannot call the name live -- the fill must precede live use.
# ported from bend3: bend3 ratified the forward call (C27); bend4 pins
# the opposite (an unfilled assert is dead-only, book order rules)
type Nz:
  Zn{}
  Sn{p: Nz}

assert twice:
  forall x : Nz
  Nz

assert early:
  forall x: Nz
  Nz

def early(x):
  twice(x)

def twice(x):
  Sn{Sn{x}}

assert main:
  Nz

def main(): early(Zn{})
$$ bend %
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : twice
Context:
- x : Nz
Location: early
17 | def early(x):
18>|   twice(x)
19 |
