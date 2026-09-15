# proof_numerics: the laws. The human states them; PROOF.bend must
# prove them. Each law is a general claim about main.bend's functions:
# (Nat, add, 0n) and (Nat, mul, 1n) are commutative monoids and mul
# distributes over add; double is adding a number to itself, half
# undoes it and its result is even; pow turns a sum of exponents into
# a product; sub undoes add; le is an order; and divmod is right: the
# remainder is below the divisor, and the quotient and remainder
# rebuild the dividend, which is Euclid's theorem.
#
# A parameter is + when a proof spends it twice and - when only the
# statement mentions it.

import Base
import ./main.bend as Num

# Addition
# --------

# LAW: add is commutative
law add_comm:
  for  a: Nat
  for +b: Nat
  {Num.add(a, b) == Num.add(b, a) : Nat}

# LAW: add is associative
law add_assoc:
  for  a: Nat
  for -b: Nat
  for -c: Nat
  {Num.add(a, Num.add(b, c)) == Num.add(Num.add(a, b), c) : Nat}

# Multiplication
# --------------

# LAW: mul is commutative
law mul_comm:
  for +a: Nat
  for +b: Nat
  {Num.mul(a, b) == Num.mul(b, a) : Nat}

# LAW: mul distributes over add: (a + b) * c is a * c + b * c
law mul_dist:
  for  a: Nat
  for -b: Nat
  for +c: Nat
  {Num.add(Num.mul(a, c), Num.mul(b, c)) == Num.mul(Num.add(a, b), c) : Nat}

# LAW: mul is associative
law mul_assoc:
  for  a: Nat
  for +b: Nat
  for +c: Nat
  {Num.mul(a, Num.mul(b, c)) == Num.mul(Num.mul(a, b), c) : Nat}

# Double, half, even
# ------------------

# LAW: double is adding a number to itself
law double_is_add:
  for +n: Nat
  {Num.double(n) == Num.add(n, n) : Nat}

# LAW: half undoes double
law half_double:
  for n: Nat
  {Num.half(Num.double(n)) == n : Nat}

# LAW: a double is even
law even_double:
  for n: Nat
  {Num.even(Num.double(n)) == True{} : Bool}

# Powers and differences
# ----------------------

# LAW: a power of a sum of exponents is the product of the powers
law pow_add:
  for +b: Nat
  for  m: Nat
  for +n: Nat
  {Num.pow(b, Num.add(m, n)) == Num.mul(Num.pow(b, m), Num.pow(b, n)) : Nat}

# LAW: sub undoes add: (a + b) - b is a
law sub_add:
  for +a: Nat
  for  b: Nat
  {Num.sub(Num.add(a, b), b) == a : Nat}

# Order
# -----

# LAW: le is transitive
law le_trans:
  for a  : Nat
  for b  : Nat
  for c  : Nat
  for ab : Num.le(a, b)
  for bc : Num.le(b, c)
  Num.le(a, c)

# LAW: le is antisymmetric
law le_antisym:
  for a  : Nat
  for b  : Nat
  for ab : Num.le(a, b)
  for ba : Num.le(b, a)
  {a == b : Nat}

# Division
# --------

# LAW: divmod is right: dividing n by the positive divisor 1n+m gives a
# remainder below the divisor, and the quotient and remainder rebuild n
law divmod_ok:
  for  n: Nat
  for +m: Nat
  Num.DivSpec(n, m, Num.divmod(n, 1n+m))

# LAW: Euclid: for every n and positive divisor 1n+m there are a
# quotient q and a remainder r below the divisor with n == q * (1n+m) + r
law euclid:
  for +n: Nat
  for +m: Nat
  exs  q: Nat
  exs  r: Nat
  Num.lt(r, 1n+m) & {n == Num.add(Num.mul(q, 1n+m), r) : Nat}
