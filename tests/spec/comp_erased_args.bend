# comp-splice pin (spec_comp_erased_args): bend3 checked erased template
# args against the REAL earlier arguments (the %s placeholder soundness
# hole, pinned rejected). a ~ clause after a plain one heads no template
# (only leading ~ clauses do), so g is an erased binder, and its live
# use in the fill is refused. (bend3's local Nat rides base's Nat; the
# fake proof would be {==} at 0n == 1n.)
import Base

law tpl:
  for a: Nat
  for b: Nat
  for -e: {a == b : Nat}
  for ~g: Nat -> Nat
  for x: Nat
  Nat

def tpl(a, b, e, g, x):
  match x:
    case 0n:
      g(a)
    case 1n+p:
      g(b)

law main:
  for x: Nat
  Nat

def main(x):
  tpl(0n, 1n, {==}, y => y, x)

#|Error:
#|- expected : -g
#|- observed : g
#|Context:
#|- a : Nat
#|- b : Nat
#|- e : {a == b : Nat}
#|Location: tpl
#|16 |
#|17>| def tpl(a, b, e, g, x):
#|18 |   match x:
#|exit 1
