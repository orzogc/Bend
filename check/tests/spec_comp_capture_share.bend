# comp-splice pin (spec_comp_capture_share): bend3's capture honesty,
# positive side -- a spliced lambda's captured runtime var kept its true
# multiplicity in the residual. bend4 has no comp surface (and its core
# is affine: a Many capture has no free contraction to ride); the ~
# binder pins bend4's own parse refusal.
import Base

type L:
  C{h: U32, t: L}
  N{}

assert apply:
  forall ~f: U32 -> U32
  forall x: U32
  U32

def apply(f, x):
  f(x)

assert once:
  forall k: U32
  forall x: U32
  U32

def once(k, x):
  apply(y => y + k, x)

assert main:
  U32

def main():
  once(10, 1)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
12 | assert apply:
13>|   forall ~f: U32 -> U32
14 |   forall x: U32
