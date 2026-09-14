# proof_numerics: the laws. The human states them; PROOF.bend must
# prove them. Each law is a claim about main.bend's add, mul and le:
# (Nat, add, 0n) and (Nat, mul, 1n) are commutative monoids, mul
# distributes over add, the successor is injective and never zero, and
# a <= b exactly when b is a plus something.
#
# A rewrite folds the right endpoint of an equation back into the
# left, so every equation is stated with the term a proof eliminates
# on the right: {1n+add(a, b) == add(a, 1n+b)} eliminates add(a, 1n+b).
# A parameter is dead (-) when no proof consumes it.

import Base
import ./main.bend as Num

# Addition
# --------

# LAW: zero is the right unit of add
law add_zero:
  for a: Nat
  {Num.add(a, 0n) == a : Nat}

# LAW: a successor on the right of add moves to the front
law add_succ:
  for  a: Nat
  for -b: Nat
  {1n+Num.add(a, b) == Num.add(a, 1n+b) : Nat}

# LAW: add is associative
law add_assoc:
  for  a: Nat
  for -b: Nat
  for -c: Nat
  {Num.add(a, Num.add(b, c)) == Num.add(Num.add(a, b), c) : Nat}

# LAW: add is commutative
law add_comm:
  for a: Nat
  for b: Nat
  {Num.add(b, a) == Num.add(a, b) : Nat}

# Multiplication
# --------------

# LAW: zero absorbs mul on the right
law mul_zero:
  for a: Nat
  {Num.mul(a, 0n) == 0n : Nat}

# LAW: one is the right unit of mul
law mul_one:
  for a: Nat
  {Num.mul(a, 1n) == a : Nat}

# LAW: a successor on the right of mul adds one more a
law mul_succ:
  for a: Nat
  for b: Nat
  {Num.add(a, Num.mul(a, b)) == Num.mul(a, 1n+b) : Nat}

# LAW: mul is commutative
law mul_comm:
  for a: Nat
  for b: Nat
  {Num.mul(b, a) == Num.mul(a, b) : Nat}

# LAW: mul distributes over add
law mul_dist:
  for  a: Nat
  for -b: Nat
  for  c: Nat
  {Num.add(Num.mul(a, c), Num.mul(b, c)) == Num.mul(Num.add(a, b), c) : Nat}

# LAW: mul is associative
law mul_assoc:
  for a: Nat
  for b: Nat
  for c: Nat
  {Num.mul(a, Num.mul(b, c)) == Num.mul(Num.mul(a, b), c) : Nat}

# Successor
# ---------

# LAW: a successor is never zero
law succ_neq_zero:
  for -a: Nat
  for  e: {1n+a == 0n : Nat}
  Empty

# LAW: the successor is injective
law succ_inj:
  for -a: Nat
  for -b: Nat
  for  e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

# Order
# -----

# LAW: when a <= b, b is a plus some c
law le_diff:
  for a: Nat
  for b: Nat
  for e: Num.le(a, b)
  (&c: Nat -> {Num.add(a, c) == b : Nat})
