# Base Equal (the equality kit over the primitive {a == b : T}):
# sym flips, trans chains, cong maps -- each usable with hypothesis
# ARGUMENTS (e : {a == b : T} params) and on concretes, where the
# proof computes to {==}.
# ported from bend3: bend4's own base carries Equal.sym/trans/cong
import Base

assert flip:
  forall -x: Nat
  forall e: {x == 3n : Nat}
  {3n == x : Nat}

def flip(x, e):
  Equal.sym(Nat, x, 3n, e)

assert chain:
  forall -x: Nat
  forall -y: Nat
  forall e1: {x == y : Nat}
  forall e2: {y == 5n : Nat}
  {x == 5n : Nat}

def chain(x, y, e1, e2):
  Equal.trans(Nat, x, y, 5n, e1, e2)

assert succ_eq:
  forall -x: Nat
  forall -y: Nat
  forall e: {x == y : Nat}
  {Succ{x} == Succ{y} : Nat}

def succ_eq(x, y, e):
  Equal.cong(Nat, Nat, n => Succ{n}, x, y, e)

assert v:
  {3n == Nat.add(1n, 2n) : Nat}

def v(): Equal.sym(Nat, Nat.add(1n, 2n), 3n, {==})

assert main:
  {3n == Nat.add(1n, 2n) : Nat}

def main(): v()

$$ bend %
{==}
