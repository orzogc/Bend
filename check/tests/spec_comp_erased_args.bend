# comp-splice pin (spec_comp_erased_args): bend3 checked erased template
# args against the REAL earlier arguments (the %s placeholder soundness
# hole, pinned rejected). bend4 has no comp surface to open that door;
# the ~ binder pins bend4's own parse refusal. (bend3's local Nat rides
# base's Nat; the fake proof would be {==} at 0n == 1n.)
import Base

assert tpl:
  forall a: Nat
  forall b: Nat
  forall -e: {a == b : Nat}
  forall ~g: Nat -> Nat
  forall x: Nat
  Nat

def tpl(a, b, e, g, x):
  match x:
    case 0n:
      g(a)
    case 1n+p:
      g(b)

assert main:
  forall x: Nat
  Nat

def main(x):
  tpl(0n, 1n, {==}, y => y, x)
$$ bend %
Error:
- expected : a name
- observed : '~'
Location:
11 |   forall -e: {a == b : Nat}
12>|   forall ~g: Nat -> Nat
13 |   forall x: Nat
