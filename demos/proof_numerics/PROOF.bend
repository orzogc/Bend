# proof_numerics: the proofs. This file imports the definitions (as
# Num) and the claims (as Laws) and fills every law as def Laws.<name>.
# A claim is a def whose return type IS the proposition and whose body
# is the proof. The rules of the game:
#
# - a live variable is consumed at most once. A match consumes its
#   scrutinee, so an induction variable's single use is the match.
# - a lemma parameter is dead (-) unless the proof truly consumes it.
#   Dead arguments cost the caller nothing and may mention spent
#   variables, so lemmas are stated to keep live positions cheap.
# - a rewrite %e : P; f spends e : {a == b} once. The motive P marks
#   occurrences of b as _: the goal must be P(b), and f proves P(a).
#   A rewrite folds the RIGHT endpoint back into the LEFT, so every
#   equation is stated with the term it eliminates on the right:
#   {replica == original}, {unfolding == mul(1n+p, b)}.
# - a recursive call must shrink the actual pattern variable, never a
#   copy of it.
#
# Num.copy2 derives duplication for Nat in CPS: copy2_spec proves the
# copy exact, and one rewrite with it turns a goal about the stuck
# copy into a goal about the plain value. Every proof that needs
# replicas opens copy2 in CPS -- a lambda-match application is a
# banned form, so there is no data-shaped copy to destructure -- and
# spends one equation per rewrite to relink the goal to the replicas;
# eqcopy2 hands back two uses of one equation the same way (an
# equation is Data, so a + binder licenses it).

import Base
import ./main.bend as Num
import ./LAWS.bend as Laws

# Copy lemmas
# -----------

# the copy is exact: the continuation on the replicas equals the
# continuation on the original
law copy2_spec:
  for  n: Nat
  for -P: Type
  for -f: @a: Nat -> @ea: {a == n : Nat} -> @b: Nat -> @eb: {b == n : Nat} -> @eab: {b == a : Nat} -> P
  {f(n, {==}, n, {==}, {==}) == Num.copy2(n, P, f) : P}

def copy2_spec(n, P, f):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %copy2_spec(p, P, a => ea => b => eb => eab =>
        f(1n+a, Equal.cong(Nat, Nat, x => 1n+x, a, p, ea),
          1n+b, Equal.cong(Nat, Nat, x => 1n+x, b, p, eb),
          Equal.cong(Nat, Nat, x => 1n+x, b, a, eab))) : {f(1n+p, {==}, 1n+p, {==}, {==}) == _ : P}
      {==}

# equations are consumed by rewrites; eqcopy2 hands back two uses of
# one, through a + binder (an equation is Data), in the same CPS shape

law eqcopy2:
  for -a: Nat
  for -b: Nat
  for +e: {a == b : Nat}
  for -P: Type
  for  f: @e1: {a == b : Nat} -> @e2: {a == b : Nat} -> P
  P

def eqcopy2(a, b, e, P, f):
  f(e, e)
# mul's second defining equation
# on an open b the copy is stuck, so mul's second defining equation is
# not conversion. copy2_spec recovers it as a theorem priced at one
# use of b.

law mul_unfold:
  for -p: Nat
  for  b: Nat
  {Num.add(b, Num.mul(p, b)) == Num.mul(1n+p, b) : Nat}

def mul_unfold(p, b):
  %copy2_spec(b, Nat, b1 => e1 => b2 => e2 => e12 => Num.add(b1, Num.mul(p, b2))) : {Num.add(b, Num.mul(p, b)) == _ : Nat}
  {==}
# Addition
# --------

# (Nat, add, 0n) is a commutative monoid

def Laws.add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_zero(p) : {1n+Num.add(p, 0n) == 1n+_ : Nat}
      {==}

def Laws.add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_succ(p, b) : {2n+Num.add(p, b) == 1n+_ : Nat}
      {==}

def Laws.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_assoc(p, b, c) : {1n+Num.add(p, Num.add(b, c)) == 1n+_ : Nat}
      {==}

# the copy pattern in the small: b1 feeds add_succ, b2 feeds the IH,
# and each equation relinks the goal once

def Laws.add_comm(a, b):
  match a:
    case 0n:
      %Laws.add_zero(b) : {Num.add(b, 0n) == _ : Nat}
      {==}
    case 1n+p:
      Num.copy2(b, {Num.add(b, 1n+p) == Num.add(1n+p, b) : Nat}, b1 => e1 => b2 => e2 => e12 =>
        %e1 : {Num.add(_, 1n+p) == 1n+Num.add(p, b) : Nat}
        %e2 : {Num.add(b1, 1n+p) == 1n+Num.add(p, _) : Nat}
        %Laws.add_succ(b1, p) : {_ == 1n+Num.add(p, b2) : Nat}
        %e12 : {1n+Num.add(_, p) == 1n+Num.add(p, b2) : Nat}
        %Laws.add_comm(p, b2) : {1n+Num.add(b2, p) == 1n+_ : Nat}
        {==})

law add_swap:
  for  a: Nat
  for  b: Nat
  for -c: Nat
  {Num.add(b, Num.add(a, c)) == Num.add(a, Num.add(b, c)) : Nat}

def add_swap(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Num.copy2(b, {Num.add(b, Num.add(1n+p, c)) == Num.add(1n+p, Num.add(b, c)) : Nat}, b1 => e1 => b2 => e2 => e12 =>
        %e1 : {Num.add(_, 1n+Num.add(p, c)) == 1n+Num.add(p, Num.add(b, c)) : Nat}
        %e2 : {Num.add(b1, 1n+Num.add(p, c)) == 1n+Num.add(p, Num.add(_, c)) : Nat}
        %Laws.add_succ(b1, Num.add(p, c)) : {_ == 1n+Num.add(p, Num.add(b2, c)) : Nat}
        %e12 : {1n+Num.add(_, Num.add(p, c)) == 1n+Num.add(p, Num.add(b2, c)) : Nat}
        %add_swap(p, b2, c) : {1n+Num.add(b2, Num.add(p, c)) == 1n+_ : Nat}
        {==})

# Multiplication
# --------------

# (Nat, mul, 1n) is a commutative monoid that distributes over add

def Laws.mul_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Laws.mul_zero(p)

def Laws.mul_one(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.mul_one(p) : {1n+Num.mul(p, 1n) == 1n+_ : Nat}
      {==}

# mul_succ and mul_comm need their induction variable a twice: once
# for the IH and once inside a lemma instance. A .go worker pays for
# that: it consumes a and hands its continuation two certified
# replicas of a beside the proof, so the level above can spend "a"
# again. That is paramorphic induction, spelled out in CPS. The
# public theorem passes a continuation that drops the replicas.

law mul_succ.go:
  for  a: Nat
  for  b: Nat
  for -P: Type
  for  f: @r1: Nat -> @u: {r1 == a : Nat} -> @r2: Nat -> @v: {r2 == a : Nat} -> @w: {Num.add(a, Num.mul(a, b)) == Num.mul(a, 1n+b) : Nat} -> P
  P

def mul_succ.go(a, b, P, f):
  match a:
    case 0n:
      f(0n, {==}, 0n, {==}, {==})
    case 1n+p:
      Num.copy2(b, P, c1 => ec1 => c2 => ec2 => sc =>
      Num.copy2(c2, P, d1 => ed1 => d2 => ed2 => sd =>
      Num.copy2(d2, P, e1 => ee1 => e2 => ee2 => se =>
      mul_succ.go(p, d1, P, p1 => u => p2 => v => ih =>
      Num.copy2(p2, P, q1 => eq1 => q2 => eq2 => sq =>
      eqcopy2(p2, p, v, P, va => vb =>
      f(1n+q1,
        %va : {1n+q1 == 1n+_ : Nat}
        %eq1 : {1n+q1 == 1n+_ : Nat}
        {==},
        1n+q2,
        %vb : {1n+q2 == 1n+_ : Nat}
        %eq2 : {1n+q2 == 1n+_ : Nat}
        {==},
        %ec1 : {1n+Num.add(p, Num.mul(1n+p, b)) == Num.mul(1n+p, 1n+_) : Nat}
        %mul_unfold(p, 1n+c1) : {1n+Num.add(p, Num.mul(1n+p, b)) == _ : Nat}
        %sc : {1n+Num.add(p, Num.mul(1n+p, b)) == 1n+Num.add(_, Num.mul(p, 1n+_)) : Nat}
        %ec2 : {1n+Num.add(p, Num.mul(1n+p, _)) == 1n+Num.add(c2, Num.mul(p, 1n+c2)) : Nat}
        %ed1 : {1n+Num.add(p, Num.mul(1n+p, _)) == 1n+Num.add(_, Num.mul(p, 1n+_)) : Nat}
        %ih : {1n+Num.add(p, Num.mul(1n+p, d1)) == 1n+Num.add(d1, _) : Nat}
        %sd : {1n+Num.add(p, Num.mul(1n+p, _)) == 1n+Num.add(_, Num.add(p, Num.mul(p, _))) : Nat}
        %ee1 : {1n+Num.add(p, Num.mul(1n+p, d2)) == 1n+Num.add(_, Num.add(p, Num.mul(p, d2))) : Nat}
        %u : {1n+Num.add(_, Num.mul(1n+p, d2)) == 1n+Num.add(e1, Num.add(_, Num.mul(p, d2))) : Nat}
        %add_swap(e1, p1, Num.mul(p, d2)) : {1n+Num.add(p1, Num.mul(1n+p, d2)) == 1n+_ : Nat}
        %se : {1n+Num.add(p1, Num.mul(1n+p, d2)) == 1n+Num.add(p1, Num.add(_, Num.mul(p, d2))) : Nat}
        %ee2 : {1n+Num.add(p1, Num.mul(1n+p, _)) == 1n+Num.add(p1, Num.add(e2, Num.mul(p, _))) : Nat}
        %mul_unfold(p, e2) : {1n+Num.add(p1, _) == 1n+Num.add(p1, Num.add(e2, Num.mul(p, e2))) : Nat}
        {==})))))))

def Laws.mul_succ(a, b):
  mul_succ.go(a, b, {Num.add(a, Num.mul(a, b)) == Num.mul(a, 1n+b) : Nat},
    r1 => u => r2 => v => w => w)

law mul_comm.go:
  for  a: Nat
  for  b: Nat
  for -P: Type
  for  f: @r1: Nat -> @u: {r1 == a : Nat} -> @r2: Nat -> @v: {r2 == a : Nat} -> @w: {Num.mul(b, a) == Num.mul(a, b) : Nat} -> P
  P

def mul_comm.go(a, b, P, f):
  match a:
    case 0n:
      f(0n, {==}, 0n, {==}, Laws.mul_zero(b))
    case 1n+p:
      Num.copy2(b, P, c1 => ec1 => c2 => ec2 => sc =>
      Num.copy2(c2, P, d1 => ed1 => d2 => ed2 => sd =>
      mul_comm.go(p, d1, P, p1 => u => p2 => v => ih =>
      Num.copy2(p2, P, q1 => eq1 => q2 => eq2 => sq =>
      eqcopy2(p2, p, v, P, va => vb =>
      f(1n+q1,
        %va : {1n+q1 == 1n+_ : Nat}
        %eq1 : {1n+q1 == 1n+_ : Nat}
        {==},
        1n+q2,
        %vb : {1n+q2 == 1n+_ : Nat}
        %eq2 : {1n+q2 == 1n+_ : Nat}
        {==},
        %ec1 : {Num.mul(b, 1n+p) == Num.mul(1n+p, _) : Nat}
        %mul_unfold(p, c1) : {Num.mul(b, 1n+p) == _ : Nat}
        %sc : {Num.mul(b, 1n+p) == Num.add(_, Num.mul(p, _)) : Nat}
        %ec2 : {Num.mul(_, 1n+p) == Num.add(c2, Num.mul(p, c2)) : Nat}
        %ed1 : {Num.mul(_, 1n+p) == Num.add(_, Num.mul(p, _)) : Nat}
        %ih : {Num.mul(d1, 1n+p) == Num.add(d1, _) : Nat}
        %sd : {Num.mul(_, 1n+p) == Num.add(_, Num.mul(_, p)) : Nat}
        %u : {Num.mul(d2, 1n+_) == Num.add(d2, Num.mul(d2, _)) : Nat}
        %Laws.mul_succ(d2, p1) : {_ == Num.add(d2, Num.mul(d2, p1)) : Nat}
        {==}))))))

def Laws.mul_comm(a, b):
  mul_comm.go(a, b, {Num.mul(b, a) == Num.mul(a, b) : Nat},
    r1 => u => r2 => v => w => w)

# distributivity and associativity spend p only on the IH, so plain
# induction suffices: no worker, just copies of c (resp. b and c)

def Laws.mul_dist(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Num.copy2(c, {Num.add(Num.mul(1n+p, c), Num.mul(b, c)) == Num.mul(Num.add(1n+p, b), c) : Nat}, c1 => ec1 => c2 => ec2 => sc =>
      Num.copy2(c2, {Num.add(Num.mul(1n+p, c), Num.mul(b, c)) == Num.mul(Num.add(1n+p, b), c) : Nat}, d1 => ed1 => d2 => ed2 => sd =>
      Num.copy2(d2, {Num.add(Num.mul(1n+p, c), Num.mul(b, c)) == Num.mul(Num.add(1n+p, b), c) : Nat}, e1 => ee1 => e2 => ee2 => se =>
      %ec1 : {Num.add(Num.mul(1n+p, c), Num.mul(b, c)) == Num.mul(1n+Num.add(p, b), _) : Nat}
      %mul_unfold(Num.add(p, b), c1) : {Num.add(Num.mul(1n+p, c), Num.mul(b, c)) == _ : Nat}
      %sc : {Num.add(Num.mul(1n+p, c), Num.mul(b, c)) == Num.add(_, Num.mul(Num.add(p, b), _)) : Nat}
      %ec2 : {Num.add(Num.mul(1n+p, _), Num.mul(b, _)) == Num.add(c2, Num.mul(Num.add(p, b), c2)) : Nat}
      %ed1 : {Num.add(Num.mul(1n+p, _), Num.mul(b, _)) == Num.add(_, Num.mul(Num.add(p, b), _)) : Nat}
      %Laws.mul_dist(p, b, d1) : {Num.add(Num.mul(1n+p, d1), Num.mul(b, d1)) == Num.add(d1, _) : Nat}
      %sd : {Num.add(Num.mul(1n+p, _), Num.mul(b, _)) == Num.add(_, Num.add(Num.mul(p, _), Num.mul(b, _))) : Nat}
      %ee1 : {Num.add(Num.mul(1n+p, _), Num.mul(b, d2)) == Num.add(d2, Num.add(Num.mul(p, d2), Num.mul(b, d2))) : Nat}
      %mul_unfold(p, e1) : {Num.add(_, Num.mul(b, d2)) == Num.add(d2, Num.add(Num.mul(p, d2), Num.mul(b, d2))) : Nat}
      %se : {Num.add(Num.add(_, Num.mul(p, _)), Num.mul(b, d2)) == Num.add(d2, Num.add(Num.mul(p, d2), Num.mul(b, d2))) : Nat}
      %Laws.add_assoc(e2, Num.mul(p, e2), Num.mul(b, d2)) : {_ == Num.add(d2, Num.add(Num.mul(p, d2), Num.mul(b, d2))) : Nat}
      %ee2 : {Num.add(e2, Num.add(Num.mul(p, e2), Num.mul(b, _))) == Num.add(_, Num.add(Num.mul(p, _), Num.mul(b, _))) : Nat}
      {==})))

def Laws.mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Num.copy2(b, {Num.mul(1n+p, Num.mul(b, c)) == Num.mul(Num.mul(1n+p, b), c) : Nat}, b1 => e1 => b2 => e2 => s12 =>
      Num.copy2(b2, {Num.mul(1n+p, Num.mul(b, c)) == Num.mul(Num.mul(1n+p, b), c) : Nat}, b3 => e3 => b4 => e4 => s34 =>
      Num.copy2(b4, {Num.mul(1n+p, Num.mul(b, c)) == Num.mul(Num.mul(1n+p, b), c) : Nat}, b5 => e5 => b6 => e6 => s56 =>
      Num.copy2(c, {Num.mul(1n+p, Num.mul(b, c)) == Num.mul(Num.mul(1n+p, b), c) : Nat}, cA => eca => cB => ecb => sAB =>
      Num.copy2(cB, {Num.mul(1n+p, Num.mul(b, c)) == Num.mul(Num.mul(1n+p, b), c) : Nat}, cC => ecc => cD => ecd => sCD =>
      %e1 : {Num.mul(1n+p, Num.mul(_, c)) == Num.mul(Num.mul(1n+p, _), c) : Nat}
      %mul_unfold(p, b1) : {Num.mul(1n+p, Num.mul(b1, c)) == Num.mul(_, c) : Nat}
      %s12 : {Num.mul(1n+p, Num.mul(_, c)) == Num.mul(Num.add(_, Num.mul(p, _)), c) : Nat}
      %e3 : {Num.mul(1n+p, Num.mul(b2, c)) == Num.mul(Num.add(_, Num.mul(p, b2)), c) : Nat}
      %eca : {Num.mul(1n+p, Num.mul(b2, _)) == Num.mul(Num.add(b3, Num.mul(p, b2)), _) : Nat}
      %Laws.mul_dist(b3, Num.mul(p, b2), cA) : {Num.mul(1n+p, Num.mul(b2, cA)) == _ : Nat}
      %e4 : {Num.mul(1n+p, Num.mul(_, cA)) == Num.add(Num.mul(b3, cA), Num.mul(Num.mul(p, _), cA)) : Nat}
      %e5 : {Num.mul(1n+p, Num.mul(_, cA)) == Num.add(Num.mul(b3, cA), Num.mul(Num.mul(p, _), cA)) : Nat}
      %sAB : {Num.mul(1n+p, Num.mul(b5, _)) == Num.add(Num.mul(b3, _), Num.mul(Num.mul(p, b5), _)) : Nat}
      %ecc : {Num.mul(1n+p, Num.mul(b5, cB)) == Num.add(Num.mul(b3, cB), Num.mul(Num.mul(p, b5), _)) : Nat}
      %ecd : {Num.mul(1n+p, Num.mul(b5, _)) == Num.add(Num.mul(b3, _), Num.mul(Num.mul(p, b5), cC)) : Nat}
      %Laws.mul_assoc(p, b5, cC) : {Num.mul(1n+p, Num.mul(b5, cD)) == Num.add(Num.mul(b3, cD), _) : Nat}
      %s56 : {Num.mul(1n+p, Num.mul(_, cD)) == Num.add(Num.mul(b3, cD), Num.mul(p, Num.mul(_, cC))) : Nat}
      %sCD : {Num.mul(1n+p, Num.mul(b6, cD)) == Num.add(Num.mul(b3, cD), Num.mul(p, Num.mul(b6, _))) : Nat}
      %mul_unfold(p, Num.mul(b6, cD)) : {_ == Num.add(Num.mul(b3, cD), Num.mul(p, Num.mul(b6, cD))) : Nat}
      %s34 : {Num.add(Num.mul(b6, cD), Num.mul(p, Num.mul(b6, cD))) == Num.add(Num.mul(_, cD), Num.mul(p, Num.mul(b6, cD))) : Nat}
      %e6 : {Num.add(Num.mul(b6, cD), Num.mul(p, Num.mul(b6, cD))) == Num.add(Num.mul(_, cD), Num.mul(p, Num.mul(b6, cD))) : Nat}
      {==})))))

# Successor
# ---------

def Laws.succ_neq_zero(a, e):
  %e : Num.discr(_)
  Unit{}

def Laws.succ_inj(a, b, e):
  %e : {a == Num.pred(_) : Nat}
  {==}

# Order
# -----

law le_diff.con:
  for -ap : Nat
  for -bp : Nat
  for w   : (&c: Nat -> {Num.add(ap, c) == bp : Nat})
  exs c   : Nat
  {1n+Num.add(ap, c) == 1n+bp : Nat}

def le_diff.con(ap, bp, w):
  (c, prf) = w
  (c, Equal.cong(Nat, Nat, x => 1n+x, Num.add(ap, c), bp, prf))

def Laws.le_diff(a, b, e):
  match a:
    case 0n:
      (b, {==})
    case 1n+ap:
      match b:
        case 0n:
          match e:
        case 1n+bp:
          le_diff.con(ap, bp, Laws.le_diff(ap, bp, e))
