# proof_numerics: the proofs. This file imports the definitions (as
# Num) and the claims (as Laws) and fills every law as def Laws.<name>.
# A claim is a def whose return type IS the proposition and whose body
# is the proof: a match on a Nat is a case analysis, the recursive call
# is the induction hypothesis, and a rewrite %e : P spends an equation
# e : {x == y} once, turning the goal P(y) into P(x). So every lemma is
# stated with the term its callers eliminate on the right.
#
# The lemma tower: add_zero and add_succ carry the commutative monoid
# of add; add_swap, mul_zero and mul_succ carry mul; sub_zero the
# difference. divmod's correctness runs through the pair it returns:
# use_spec opens a DivSpec certificate on any pair, and wrap_ok decides
# the wrap with the Bool-inspect idiom (the goal abstracted over the
# verdict b, with an equation {b == eqn(r, m)} to spend in each arm).

import Base
import ./main.bend as Num
import ./LAWS.bend as Laws

# Addition
# --------

def add_zero(a: Nat) -> {a == Num.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Num.add(a, b) == Num.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Num.add(p, b) == 1n+_ : Nat}
      {==}

def Laws.add_comm(a, b):
  match a:
    case 0n:
      %add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %add_succ(b, p) : {1n+Num.add(p, b) == _ : Nat}
      %Laws.add_comm(p, b) : {1n+Num.add(p, b) == 1n+_ : Nat}
      {==}

def Laws.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_assoc(p, b, c) : {1n+Num.add(p, Num.add(b, c)) == 1n+_ : Nat}
      {==}

# the middle terms of a triple sum swap
def add_swap(x: Nat, +y: Nat, +z: Nat) -> {Num.add(x, Num.add(y, z)) == Num.add(y, Num.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Num.add(q, z)) : {1n+Num.add(q, Num.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Num.add(q, Num.add(y, z)) == 1n+_ : Nat}
      {==}

# Multiplication
# --------------

def mul_zero(a: Nat) -> {Num.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def mul_succ(+a: Nat, +b: Nat) -> {Num.add(a, Num.mul(a, b)) == Num.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_succ(p, b) : {1n+Num.add(p, Num.add(b, Num.mul(p, b))) == 1n+Num.add(b, _) : Nat}
      %add_swap(p, b, Num.mul(p, b)) : {1n+Num.add(p, Num.add(b, Num.mul(p, b))) == 1n+_ : Nat}
      {==}

def Laws.mul_comm(a, b):
  match a:
    case 0n:
      %mul_zero(b) : {_ == Num.mul(b, 0n) : Nat}
      {==}
    case 1n++p:
      %mul_succ(b, p) : {Num.add(b, Num.mul(p, b)) == _ : Nat}
      %Laws.mul_comm(p, b) : {Num.add(b, Num.mul(p, b)) == Num.add(b, _) : Nat}
      {==}

def Laws.mul_dist(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.mul_dist(p, b, c) : {Num.add(Num.add(c, Num.mul(p, c)), Num.mul(b, c)) == Num.add(c, _) : Nat}
      %Laws.add_assoc(c, Num.mul(p, c), Num.mul(b, c)) : {_ == Num.add(c, Num.add(Num.mul(p, c), Num.mul(b, c))) : Nat}
      {==}

def Laws.mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.mul_dist(b, Num.mul(p, b), c) : {Num.add(Num.mul(b, c), Num.mul(p, Num.mul(b, c))) == _ : Nat}
      %Laws.mul_assoc(p, b, c) : {Num.add(Num.mul(b, c), Num.mul(p, Num.mul(b, c))) == Num.add(Num.mul(b, c), _) : Nat}
      {==}

# Double, half, even
# ------------------

def Laws.double_is_add(n):
  match n:
    case 0n:
      {==}
    case 1n++p:
      %add_succ(p, p) : {2n+Num.double(p) == 1n+_ : Nat}
      %Laws.double_is_add(p) : {2n+Num.double(p) == 2n+_ : Nat}
      {==}

def Laws.half_double(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Laws.half_double(p) : {1n+Num.half(Num.double(p)) == 1n+_ : Nat}
      {==}

def Laws.even_double(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, Num.even(Num.double(p)), True{}, Laws.even_double(p)) : {Bool.not(Bool.not(_)) == True{} : Bool}
      {==}

# Powers and differences
# ----------------------

def Laws.pow_add(b, m, n):
  match m:
    case 0n:
      %add_zero(Num.pow(b, n)) : {Num.pow(b, n) == _ : Nat}
      {==}
    case 1n++p:
      %Laws.mul_assoc(b, Num.pow(b, p), Num.pow(b, n)) : {Num.mul(b, Num.pow(b, Num.add(p, n))) == _ : Nat}
      %Laws.pow_add(b, p, n) : {Num.mul(b, Num.pow(b, Num.add(p, n))) == Num.mul(b, _) : Nat}
      {==}

def sub_zero(a: Nat) -> {Num.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.sub_add(a, b):
  match b:
    case 0n:
      %add_zero(a) : {Num.sub(_, 0n) == a : Nat}
      sub_zero(a)
    case 1n+q:
      %add_succ(a, q) : {Num.sub(_, 1n+q) == a : Nat}
      Laws.sub_add(a, q)

# Order
# -----

def Laws.le_trans(a, b, c, ab, bc):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(Num.le(1n+x, c), ab)
        case 1n+y:
          match c:
            case 0n:
              Empty.absurd(Num.le(1n+x, 0n), bc)
            case 1n+z:
              Laws.le_trans(x, y, z, ab, bc)

def Laws.le_antisym(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      Empty.absurd({0n == 1n+y : Nat}, ba)
    case 1n+x 0n:
      Empty.absurd({1n+x == 0n : Nat}, ab)
    case 1n+x 1n+y:
      Equal.cong(Nat, Nat, k => 1n+k, x, y, Laws.le_antisym(x, y, ab, ba))

# Division
# --------

# BD(b, t, f) picks a type by a Bool, so a rewrite through it refutes
# a clash between True{} and False{}
def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

# eqn is sound: a True verdict is an equation
def eq_sound(r: Nat, m: Nat, e: {True{} == Num.eqn(r, m) : Bool}) -> {r == m : Nat}:
  match r m:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      %e : BD(_, Unit, {0n == 1n+b : Nat})
      Unit{}
    case 1n+a 0n:
      %e : BD(_, Unit, {1n+a == 0n : Nat})
      Unit{}
    case 1n+a 1n+b:
      %eq_sound(a, b, e) : {1n+a == 1n+_ : Nat}
      {==}

# a remainder below the divisor that differs from m stays below it
# when bumped
def le_bump(r: Nat, m: Nat, lt: Num.le(r, m), e: {False{} == Num.eqn(r, m) : Bool}) -> Num.le(1n+r, m):
  match r m:
    case 0n 0n:
      %e : BD(_, Empty, Unit)
      Unit{}
    case 0n 1n+b:
      Unit{}
    case 1n+a 0n:
      match lt:
    case 1n+a 1n+b:
      le_bump(a, b, lt, e)

# the wrap arm: q + 1 and 0n rebuild 1n+p when r was m
def wrap_t(-p: Nat, +m: Nat, +q: Nat, -r: Nat, eq: {p == Num.add(Num.mul(q, 1n+m), r) : Nat}, rm: {r == m : Nat})
  -> {1n+p == Num.add(Num.mul(1n+q, 1n+m), 0n) : Nat}:
  %add_zero(Num.add(m, Num.mul(q, 1n+m))) : {1n+p == 1n+_ : Nat}
  %Laws.add_comm(Num.mul(q, 1n+m), m) : {1n+p == 1n+_ : Nat}
  %rm : {1n+p == 1n+Num.add(Num.mul(q, 1n+m), _) : Nat}
  %eq : {1n+p == 1n+_ : Nat}
  {==}

# the bump arm: q and r + 1 rebuild 1n+p
def wrap_f(-p: Nat, m: Nat, q: Nat, -r: Nat, eq: {p == Num.add(Num.mul(q, 1n+m), r) : Nat})
  -> {1n+p == Num.add(Num.mul(q, 1n+m), 1n+r) : Nat}:
  %add_succ(Num.mul(q, 1n+m), r) : {1n+p == _ : Nat}
  %eq : {1n+p == 1n+_ : Nat}
  {==}

# the step keeps the spec, decided on the verdict b of eqn(r, m)
def wrap_ok(-p: Nat, +m: Nat, q: Nat, r: Nat, lt: Num.le(r, m), eq: {p == Num.add(Num.mul(q, 1n+m), r) : Nat},
  b: Bool, e: {b == Num.eqn(r, m) : Bool}) -> Num.DivSpec(1n+p, m, Num.divmod.wrap(b, q, r)):
  match b:
    case True{}:
      (Unit{}, wrap_t(p, m, q, r, eq, eq_sound(r, m, e)))
    case False{}:
      (le_bump(r, m, lt, e), wrap_f(p, m, q, r, eq))

def step_ok(-p: Nat, +m: Nat, q: Nat, +r: Nat, lt: Num.le(r, m), eq: {p == Num.add(Num.mul(q, 1n+m), r) : Nat})
  -> Num.DivSpec(1n+p, m, Num.divmod.step(m, (q, r))):
  wrap_ok(p, m, q, r, lt, eq, Num.eqn(r, m), {==})

# opens a DivSpec certificate on a pair for a goal about that pair
def use_spec(-n: Nat, -m: Nat, qr: Nat & Nat, w: Num.DivSpec(n, m, qr), -P: (Nat & Nat) -> Type,
  k: @q: Nat -> @r: Nat -> Num.le(r, m) -> {n == Num.add(Num.mul(q, 1n+m), r) : Nat} -> P((q, r))) -> P(qr):
  (q, r) = qr
  (lt, eq) = w
  k(q, r, lt, eq)

# induction on n: the zero step is (0n, 0n); a successor step opens
# the certificate of divmod.go(p, m) and runs it through step_ok
def Laws.divmod_ok(n, m):
  match n:
    case 0n:
      (Unit{}, {==})
    case 1n++p:
      use_spec(p, m, Num.divmod.go(p, m), Laws.divmod_ok(p, m),
        qr => Num.DivSpec(1n+p, m, Num.divmod.step(m, qr)),
        q => r => lt => eq => step_ok(p, m, q, r, lt, eq))

# the witnesses are divmod's own quotient and remainder
def Laws.euclid(n, m):
  use_spec(n, m, Num.divmod.go(n, m), Laws.divmod_ok(n, m),
    qr => (&q: Nat -> &r: Nat -> Num.lt(r, 1n+m) & {n == Num.add(Num.mul(q, 1n+m), r) : Nat}),
    q => r => lt => eq => (q, r, lt, eq))
