# the Cop condition binds Let formation: a + let binder licenses
# contraction, so its inferred type must be a Cop (+ T ~ C).
# gutted, +x = a duplicates an affine value freely and this
# program answers Tuple{1n, 1n}.
import Base

assert dupl:
  forall a: Nat
  Nat & Nat

def dupl(a):
  +x = a
  (x, x)

assert main:
  Nat & Nat

def main(): dupl(1n)
$$ bend %
Error:
- expected : a copiable type (a + binder needs a + T ~ C type)
- observed : Tuple{a, a}
Context:
- a : Nat
Location: dupl
11 | def dupl(a):
12>|   +x = a
13 |   (x, x)
