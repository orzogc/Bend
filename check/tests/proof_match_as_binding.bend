# `match E as e` bound each arm's own equation {E = pattern} in bend3
# -- evidence minted by the elaborator, not by any parser. bend4's
# match has no as-binder by ruling (the feature program admits it
# "only if simple", and an equation binder needs the checker to mint
# per-arm evidence: not a parser-and-shower sugar), so the surface
# refuses: `as` parses as a second scrutinee and the arm arity law
# rejects the shape. The proof idiom bend4 rules instead -- factor the
# branching decision into a helper def and cong over it -- is pinned
# by the ported proof corpus (proof_parity_double_wrap's par2.go).
# ported from bend3: the golden is bend4's own refusal
import Base

assert Nat.is_eq:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

assert award:
  forall h: Nat
  forall i: Nat
  Nat

def award(h, i):
  match Nat.is_eq(h, i) as e:
    case True{}:
      h
    case False{}:
      i

assert main:
  Nat

def main():
  award(3n, 3n)
$$ bend %
Error:
- expected : 3 patterns (one per scrutinee)
- observed : '
'
Location:
27 |   match Nat.is_eq(h, i) as e:
28>|     case True{}:
29 |       h
