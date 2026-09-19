# comp-splice pin (spec_comp_capture_share): bend3's capture honesty,
# positive side -- a spliced lambda's captured runtime var kept its true
# multiplicity in the residual. bend's core is affine (a Many capture
# has no free contraction to ride); bend's ~ law apply checks once, f an
# opaque constant; the call passes f without ~, so the instance binds f
# as an erased runtime binder, and its live use is refused.
import Base

type L is Data:
  C{h: U32, t: L}
  N{}

law apply:
  for ~f: U32 -> U32
  for x: U32
  U32

def apply(f, x):
  f(x)

law once:
  for k: U32
  for x: U32
  U32

def once(k, x):
  apply(y => (y + k : U32), x)

law main:
  U32

def main():
  once(10, 1)

#|Error:
#|- expected : -f
#|- observed : f
#|Location: apply~0
#|17 |
#|18>| def apply(f, x):
#|19 |   f(x)
#|exit 1
