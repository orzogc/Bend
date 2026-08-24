# comp-splice pin (spec_comp_curried_lambda): bend3's curried comp arrows
# took x => y => chains as spliced arguments. bend4 has no comp surface;
# the ~ binder pins bend4's own parse refusal.
import Base

assert app2:
  forall ~f: U32 -> U32 -> U32
  forall a: U32
  forall b: U32
  U32

def app2(f, a, b):
  f(a, b)

assert helper:
  forall x: U32
  U32

def helper(x):
  x * x

assert main:
  U32

def main():
  app2(x => y => (x * 10) + y, 3, 4) + helper(2)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
6 | assert app2:
7>|   forall ~f: U32 -> U32 -> U32
8 |   forall a: U32
