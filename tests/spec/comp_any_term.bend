# comp-splice pin (spec_comp_any_term): bend3 filled a comp (~) slot
# with ANY term (a ref, a runtime-bound lambda var). bend's ~ law use
# checks once, f an opaque constant; the call passes f without ~, so the
# instance binds f as an erased runtime binder, and its live use is
# refused.
import Base

law use:
  for ~f: U32 -> U32
  for x: U32
  U32

def use(f, x):
  f(x)

law inc:
  for x: U32
  U32

def inc(x):
  (x + 1 : U32)

law caller:
  for x: U32
  U32

def caller(x):
  g = {y => (y + 1 : U32) : U32 -> U32}
  use(g, x)

law main:
  U32

def main():
  (caller(3) * 10 + use(inc, 5) : U32)

#|Error:
#|- expected : -f
#|- observed : f
#|Location: use~0
#|12 |
#|13>| def use(f, x):
#|14 |   f(x)
#|exit 1
