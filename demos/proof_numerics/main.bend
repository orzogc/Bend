# proof_numerics: the arithmetic of the unary naturals in the affine
# core. This file defines add, mul and the order le on Base's Nat, and
# prints mul(6n, 7n). LAWS.bend states the algebra these definitions
# obey (a commutative semiring, an injective successor, an order that
# is a difference); PROOF.bend proves it.
#
#   bend demos/proof_numerics/main.bend
#
# Duplication is not primitive here: copy2 derives it for Nat at
# spelled O(n) cost, in CPS so that the defs built on it (mul) stay
# unfoldable. It consumes n once and continues with two replicas and
# the three equations that relate them; the proofs spend those
# equations.

import Base

# Copying
# -------

# contraction as a theorem-with-cost: consume n once, continue with two
# replicas and the three equations relating them
def copy2(n: Nat, -P: Type, f: @a: Nat -> @ea: {a == n : Nat} -> @b: Nat -> @eb: {b == n : Nat} -> @eab: {b == a : Nat} -> P) -> P:
  match n:
    case 0n:
      f(0n, {==}, 0n, {==}, {==})
    case 1n+p:
      copy2(p, P, a => ea => b => eb => eab =>
        f(1n+a, Equal.cong(Nat, Nat, x => 1n+x, a, p, ea),
          1n+b, Equal.cong(Nat, Nat, x => 1n+x, b, p, eb),
          Equal.cong(Nat, Nat, x => 1n+x, b, a, eab)))

# Arithmetic
# ----------

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+add(p, b)

# mul spends b twice per step, so it copies it
def mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      copy2(b, Nat, b1 => e1 => b2 => e2 => e12 => add(b1, mul(p, b2)))

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# Order
# -----

# a Type computed by match: Empty at zero, Unit at a successor
def discr(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

# le is a computed type: Unit when a <= b holds, Empty when it fails
def le(a: Nat, b: Nat) -> Type:
  match a:
    case 0n:
      Unit
    case 1n+ap:
      match b:
        case 0n:
          Empty
        case 1n+bp:
          le(ap, bp)

# Main
# ----

def main() -> Nat:
  mul(6n, 7n)
