# comp-splice pin (spec_comp_any_term): bend3 filled a comp (~) slot with
# ANY term (a ref, a runtime-bound lambda var). bend4 has no comp surface
# by ruling -- the ~ binder pins bend4's own parse refusal.
import Base

assert use:
  forall ~f: U32 -> U32
  forall x: U32
  U32

def use(f, x):
  f(x)

assert inc:
  forall x: U32
  U32

def inc(x):
  x + 1

assert caller:
  forall x: U32
  U32

def caller(x):
  g = {y => y + 1 : U32 -> U32}
  use(g, x)

assert main:
  U32

def main():
  (caller(3) * 10) + use(inc, 5)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
6 | assert use:
7>|   forall ~f: U32 -> U32
8 |   forall x: U32
