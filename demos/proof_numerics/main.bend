# proof_numerics: arithmetic on Base's Nat, with its algebra proven.
# This file defines add, mul, double, half, even, pow, sub, the order
# le and a divmod on Nat, each by structural recursion, and prints
# pow(2n, 10n) beside divmod(1024n, 7n). LAWS.bend states the algebra
# these definitions obey (a commutative semiring, the double and half
# pair, the exponent law, the order, and the correctness of divmod);
# PROOF.bend proves it, by induction.
#
#   bend demos/proof_numerics/main.bend
#
# Nat is Data, so a parameter that a body spends twice is marked +:
# mul spends b once per step and once in the recursion, pow its base,
# divmod its divisor.

import Base

# Arithmetic
# ----------

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+add(p, b)

def mul(a: Nat, +b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      add(b, mul(p, b))

def double(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+double(p)

def half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+q:
      match q:
        case 0n:
          0n
        case 1n+p:
          1n+half(p)

def even(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.not(even(p))

def pow(+b: Nat, e: Nat) -> Nat:
  match e:
    case 0n:
      1n
    case 1n+p:
      mul(b, pow(b, p))

# truncated: sub(a, b) is 0n when b exceeds a
def sub(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b0:
      0n
    case 1n+ap 0n:
      1n+ap
    case 1n+ap 1n+bp:
      sub(ap, bp)

# Order
# -----

# le(a, b) is the type of proofs of a <= b: Unit when it holds, Empty
# when it fails
def le(a: Nat, b: Nat) -> Type:
  match a b:
    case 0n b0:
      Unit
    case 1n+ap 0n:
      Empty
    case 1n+ap 1n+bp:
      le(ap, bp)

def lt(a: Nat, b: Nat) -> Type:
  le(1n+a, b)

def eqn(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+bp:
      False{}
    case 1n+ap 0n:
      False{}
    case 1n+ap 1n+bp:
      eqn(ap, bp)

# Division
# --------
# divmod.go(n, m) divides n by 1n+m in n steps. A step bumps the
# remainder; when it would reach the divisor (r equals m) it wraps
# the remainder to 0n and bumps the quotient instead.

def divmod.wrap(b: Bool, q: Nat, r: Nat) -> Nat & Nat:
  match b:
    case True{}:
      (1n+q, 0n)
    case False{}:
      (q, 1n+r)

def divmod.step(+m: Nat, qr: Nat & Nat) -> Nat & Nat:
  (q, r0) = qr
  +r = r0
  divmod.wrap(eqn(r, m), q, r)

def divmod.go(n: Nat, +m: Nat) -> Nat & Nat:
  match n:
    case 0n:
      (0n, 0n)
    case 1n+p:
      divmod.step(m, divmod.go(p, m))

# the quotient and remainder of n by d; by 0n, (0n, n)
def divmod(n: Nat, d: Nat) -> Nat & Nat:
  match d:
    case 0n:
      (0n, n)
    case 1n+m:
      divmod.go(n, m)

# Spec
# ----

# DivSpec(n, m, (q, r)): r is below the divisor 1n+m, and the quotient
# and remainder rebuild n
def DivSpec(n: Nat, m: Nat, qr: Nat & Nat) -> Type:
  (q, r) = qr
  lt(r, 1n+m) & {n == add(mul(q, 1n+m), r) : Nat}

# Main
# ----

def main() -> Nat & (Nat & Nat):
  (pow(2n, 10n), divmod(1024n, 7n))
