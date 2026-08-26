# nat_proofs: the arithmetic of the unary naturals in the affine core.
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
#   equation below is stated with the term it eliminates on the right:
#   {replica == original}, {unfolding == mul(1n+p, b)}.
# - a recursive call must shrink the actual pattern variable, never a
#   copy of it.
#
# Duplication is not primitive; copy2 derives it for Nat at spelled
# O(n) cost, in CPS so that defs built on it (mul) stay unfoldable:
# copy2_spec proves the copy exact, and one rewrite with it turns a
# goal about the stuck copy into a goal about the plain value. Every
# proof that needs replicas opens copy2 in CPS -- a lambda-match
# application is a banned form, so there is no data-shaped copy to
# destructure -- and spends one equation per rewrite to relink the
# goal to the replicas; eqcopy2 duplicates a spent equation the same
# way.

import Base

# contraction as a theorem-with-cost: consume n once, continue with two
# replicas and the three equations relating them. The equations are
# what proofs actually spend.

assert copy2:
  forall n: Nat
  forall -P: Type
  forall f: @a: Nat -> @ea: {a == n : Nat} -> @b: Nat -> @eb: {b == n : Nat} -> @eab: {b == a : Nat} -> P
  P

def copy2(n, P, f):
  match n:
    case 0n:
      f(0n, {==}, 0n, {==}, {==})
    case 1n+p:
      copy2(p, P, a => ea => b => eb => eab =>
        f(1n+a, %ea : {1n+a == 1n+_ : Nat}; {==}, 1n+b, %eb : {1n+b == 1n+_ : Nat}; {==}, %eab : {1n+b == 1n+_ : Nat}; {==}))

assert copy2_spec:
  forall n: Nat
  forall -P: Type
  forall -f: @a: Nat -> @ea: {a == n : Nat} -> @b: Nat -> @eb: {b == n : Nat} -> @eab: {b == a : Nat} -> P
  {f(n, {==}, n, {==}, {==}) == copy2(n, P, f) : P}

def copy2_spec(n, P, f):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %copy2_spec(p, P, a => ea => b => eb => eab =>
        f(1n+a, %ea : {1n+a == 1n+_ : Nat}; {==}, 1n+b, %eb : {1n+b == 1n+_ : Nat}; {==}, %eab : {1n+b == 1n+_ : Nat}; {==})) : {f(1n+p, {==}, 1n+p, {==}, {==}) == _ : P}
      {==}

# equations are consumed by rewrites; eqcopy2 hands back two replicas
# of one, through base's Equal.copy, in the same CPS shape

assert eqsplit:
  forall -a: Nat
  forall -b: Nat
  forall -e: {a == b : Nat}
  forall -P: Type
  forall f: @e1: {a == b : Nat} -> @e2: {a == b : Nat} -> P
  forall c: Copy({a == b : Nat}, e) & Copy({a == b : Nat}, e)
  P

def eqsplit(a, b, e, P, f, c):
  ((x, u1), (y, u2)) = c
  f(x, y)

assert eqcopy2:
  forall -a: Nat
  forall -b: Nat
  forall e: {a == b : Nat}
  forall -P: Type
  forall f: @e1: {a == b : Nat} -> @e2: {a == b : Nat} -> P
  P

def eqcopy2(a, b, e, P, f):
  eqsplit(a, b, e, P, f, Equal.copy(Nat, a, b, e))

assert add:
  forall a: Nat
  forall b: Nat
  Nat

def add(a, b):
  match a:
    case 0n:
      b
    case 1n+p:
      1n+add(p, b)

# mul spends b twice per step, so it copies it

assert mul:
  forall a: Nat
  forall b: Nat
  Nat

def mul(a, b):
  match a:
    case 0n:
      0n
    case 1n+p:
      copy2(b, Nat, b1 => e1 => b2 => e2 => e12 => add(b1, mul(p, b2)))

# on an open b the copy is stuck, so mul's second defining equation is
# not conversion. copy2_spec recovers it as a theorem priced at one
# use of b.

assert mul_unfold:
  forall -p: Nat
  forall b: Nat
  {add(b, mul(p, b)) == mul(1n+p, b) : Nat}

def mul_unfold(p, b):
  %copy2_spec(b, Nat, b1 => e1 => b2 => e2 => e12 => add(b1, mul(p, b2))) : {add(b, mul(p, b)) == _ : Nat}
  {==}

# (Nat, add, 0n) is a commutative monoid

assert add_zero:
  forall a: Nat
  {add(a, 0n) == a : Nat}

def add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+add(p, 0n) == 1n+_ : Nat}
      {==}

assert add_succ:
  forall a: Nat
  forall -b: Nat
  {1n+add(a, b) == add(a, 1n+b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+add(p, b) == 1n+_ : Nat}
      {==}

assert add_assoc:
  forall a: Nat
  forall -b: Nat
  forall -c: Nat
  {add(a, add(b, c)) == add(add(a, b), c) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+add(p, add(b, c)) == 1n+_ : Nat}
      {==}

# the copy pattern in the small: b1 feeds add_succ, b2 feeds the IH,
# and each equation relinks the goal once

assert add_comm:
  forall a: Nat
  forall b: Nat
  {add(b, a) == add(a, b) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      %add_zero(b) : {add(b, 0n) == _ : Nat}
      {==}
    case 1n+p:
      copy2(b, {add(b, 1n+p) == add(1n+p, b) : Nat}, b1 => e1 => b2 => e2 => e12 =>
        %e1 : {add(_, 1n+p) == 1n+add(p, b) : Nat}
        %e2 : {add(b1, 1n+p) == 1n+add(p, _) : Nat}
        %add_succ(b1, p) : {_ == 1n+add(p, b2) : Nat}
        %e12 : {1n+add(_, p) == 1n+add(p, b2) : Nat}
        %add_comm(p, b2) : {1n+add(b2, p) == 1n+_ : Nat}
        {==})

assert add_swap:
  forall a: Nat
  forall b: Nat
  forall -c: Nat
  {add(b, add(a, c)) == add(a, add(b, c)) : Nat}

def add_swap(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      copy2(b, {add(b, add(1n+p, c)) == add(1n+p, add(b, c)) : Nat}, b1 => e1 => b2 => e2 => e12 =>
        %e1 : {add(_, 1n+add(p, c)) == 1n+add(p, add(b, c)) : Nat}
        %e2 : {add(b1, 1n+add(p, c)) == 1n+add(p, add(_, c)) : Nat}
        %add_succ(b1, add(p, c)) : {_ == 1n+add(p, add(b2, c)) : Nat}
        %e12 : {1n+add(_, add(p, c)) == 1n+add(p, add(b2, c)) : Nat}
        %add_swap(p, b2, c) : {1n+add(b2, add(p, c)) == 1n+_ : Nat}
        {==})

# (Nat, mul, 1n) is a commutative monoid that distributes over add

assert mul_zero:
  forall a: Nat
  {mul(a, 0n) == 0n : Nat}

def mul_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

assert mul_one:
  forall a: Nat
  {mul(a, 1n) == a : Nat}

def mul_one(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_one(p) : {1n+mul(p, 1n) == 1n+_ : Nat}
      {==}

# mul_succ and mul_comm need their induction variable a twice: once
# for the IH and once inside a lemma instance. A .go worker pays for
# that: it consumes a and hands its continuation two certified
# replicas of a beside the proof, so the level above can spend "a"
# again. That is paramorphic induction, spelled out in CPS. The
# public theorem passes a continuation that drops the replicas.

assert mul_succ.go:
  forall a: Nat
  forall b: Nat
  forall -P: Type
  forall f: @r1: Nat -> @u: {r1 == a : Nat} -> @r2: Nat -> @v: {r2 == a : Nat} -> @w: {add(a, mul(a, b)) == mul(a, 1n+b) : Nat} -> P
  P

def mul_succ.go(a, b, P, f):
  match a:
    case 0n:
      f(0n, {==}, 0n, {==}, {==})
    case 1n+p:
      copy2(b, P, c1 => ec1 => c2 => ec2 => sc =>
      copy2(c2, P, d1 => ed1 => d2 => ed2 => sd =>
      copy2(d2, P, e1 => ee1 => e2 => ee2 => se =>
      mul_succ.go(p, d1, P, p1 => u => p2 => v => ih =>
      copy2(p2, P, q1 => eq1 => q2 => eq2 => sq =>
      eqcopy2(p2, p, v, P, va => vb =>
      f(1n+q1,
        %va : {1n+q1 == 1n+_ : Nat}
        %eq1 : {1n+q1 == 1n+_ : Nat}
        {==},
        1n+q2,
        %vb : {1n+q2 == 1n+_ : Nat}
        %eq2 : {1n+q2 == 1n+_ : Nat}
        {==},
        %ec1 : {1n+add(p, mul(1n+p, b)) == mul(1n+p, 1n+_) : Nat}
        %mul_unfold(p, 1n+c1) : {1n+add(p, mul(1n+p, b)) == _ : Nat}
        %sc : {1n+add(p, mul(1n+p, b)) == 1n+add(_, mul(p, 1n+_)) : Nat}
        %ec2 : {1n+add(p, mul(1n+p, _)) == 1n+add(c2, mul(p, 1n+c2)) : Nat}
        %ed1 : {1n+add(p, mul(1n+p, _)) == 1n+add(_, mul(p, 1n+_)) : Nat}
        %ih : {1n+add(p, mul(1n+p, d1)) == 1n+add(d1, _) : Nat}
        %sd : {1n+add(p, mul(1n+p, _)) == 1n+add(_, add(p, mul(p, _))) : Nat}
        %ee1 : {1n+add(p, mul(1n+p, d2)) == 1n+add(_, add(p, mul(p, d2))) : Nat}
        %u : {1n+add(_, mul(1n+p, d2)) == 1n+add(e1, add(_, mul(p, d2))) : Nat}
        %add_swap(e1, p1, mul(p, d2)) : {1n+add(p1, mul(1n+p, d2)) == 1n+_ : Nat}
        %se : {1n+add(p1, mul(1n+p, d2)) == 1n+add(p1, add(_, mul(p, d2))) : Nat}
        %ee2 : {1n+add(p1, mul(1n+p, _)) == 1n+add(p1, add(e2, mul(p, _))) : Nat}
        %mul_unfold(p, e2) : {1n+add(p1, _) == 1n+add(p1, add(e2, mul(p, e2))) : Nat}
        {==})))))))

assert mul_succ:
  forall a: Nat
  forall b: Nat
  {add(a, mul(a, b)) == mul(a, 1n+b) : Nat}

def mul_succ(a, b):
  mul_succ.go(a, b, {add(a, mul(a, b)) == mul(a, 1n+b) : Nat},
    r1 => u => r2 => v => w => w)

assert mul_comm.go:
  forall a: Nat
  forall b: Nat
  forall -P: Type
  forall f: @r1: Nat -> @u: {r1 == a : Nat} -> @r2: Nat -> @v: {r2 == a : Nat} -> @w: {mul(b, a) == mul(a, b) : Nat} -> P
  P

def mul_comm.go(a, b, P, f):
  match a:
    case 0n:
      f(0n, {==}, 0n, {==}, mul_zero(b))
    case 1n+p:
      copy2(b, P, c1 => ec1 => c2 => ec2 => sc =>
      copy2(c2, P, d1 => ed1 => d2 => ed2 => sd =>
      mul_comm.go(p, d1, P, p1 => u => p2 => v => ih =>
      copy2(p2, P, q1 => eq1 => q2 => eq2 => sq =>
      eqcopy2(p2, p, v, P, va => vb =>
      f(1n+q1,
        %va : {1n+q1 == 1n+_ : Nat}
        %eq1 : {1n+q1 == 1n+_ : Nat}
        {==},
        1n+q2,
        %vb : {1n+q2 == 1n+_ : Nat}
        %eq2 : {1n+q2 == 1n+_ : Nat}
        {==},
        %ec1 : {mul(b, 1n+p) == mul(1n+p, _) : Nat}
        %mul_unfold(p, c1) : {mul(b, 1n+p) == _ : Nat}
        %sc : {mul(b, 1n+p) == add(_, mul(p, _)) : Nat}
        %ec2 : {mul(_, 1n+p) == add(c2, mul(p, c2)) : Nat}
        %ed1 : {mul(_, 1n+p) == add(_, mul(p, _)) : Nat}
        %ih : {mul(d1, 1n+p) == add(d1, _) : Nat}
        %sd : {mul(_, 1n+p) == add(_, mul(_, p)) : Nat}
        %u : {mul(d2, 1n+_) == add(d2, mul(d2, _)) : Nat}
        %mul_succ(d2, p1) : {_ == add(d2, mul(d2, p1)) : Nat}
        {==}))))))

assert mul_comm:
  forall a: Nat
  forall b: Nat
  {mul(b, a) == mul(a, b) : Nat}

def mul_comm(a, b):
  mul_comm.go(a, b, {mul(b, a) == mul(a, b) : Nat},
    r1 => u => r2 => v => w => w)

# distributivity and associativity spend p only on the IH, so plain
# induction suffices: no worker, just copies of c (resp. b and c)

assert mul_dist:
  forall a: Nat
  forall -b: Nat
  forall c: Nat
  {add(mul(a, c), mul(b, c)) == mul(add(a, b), c) : Nat}

def mul_dist(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      copy2(c, {add(mul(1n+p, c), mul(b, c)) == mul(add(1n+p, b), c) : Nat}, c1 => ec1 => c2 => ec2 => sc =>
      copy2(c2, {add(mul(1n+p, c), mul(b, c)) == mul(add(1n+p, b), c) : Nat}, d1 => ed1 => d2 => ed2 => sd =>
      copy2(d2, {add(mul(1n+p, c), mul(b, c)) == mul(add(1n+p, b), c) : Nat}, e1 => ee1 => e2 => ee2 => se =>
      %ec1 : {add(mul(1n+p, c), mul(b, c)) == mul(1n+add(p, b), _) : Nat}
      %mul_unfold(add(p, b), c1) : {add(mul(1n+p, c), mul(b, c)) == _ : Nat}
      %sc : {add(mul(1n+p, c), mul(b, c)) == add(_, mul(add(p, b), _)) : Nat}
      %ec2 : {add(mul(1n+p, _), mul(b, _)) == add(c2, mul(add(p, b), c2)) : Nat}
      %ed1 : {add(mul(1n+p, _), mul(b, _)) == add(_, mul(add(p, b), _)) : Nat}
      %mul_dist(p, b, d1) : {add(mul(1n+p, d1), mul(b, d1)) == add(d1, _) : Nat}
      %sd : {add(mul(1n+p, _), mul(b, _)) == add(_, add(mul(p, _), mul(b, _))) : Nat}
      %ee1 : {add(mul(1n+p, _), mul(b, d2)) == add(d2, add(mul(p, d2), mul(b, d2))) : Nat}
      %mul_unfold(p, e1) : {add(_, mul(b, d2)) == add(d2, add(mul(p, d2), mul(b, d2))) : Nat}
      %se : {add(add(_, mul(p, _)), mul(b, d2)) == add(d2, add(mul(p, d2), mul(b, d2))) : Nat}
      %add_assoc(e2, mul(p, e2), mul(b, d2)) : {_ == add(d2, add(mul(p, d2), mul(b, d2))) : Nat}
      %ee2 : {add(e2, add(mul(p, e2), mul(b, _))) == add(_, add(mul(p, _), mul(b, _))) : Nat}
      {==})))

assert mul_assoc:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  {mul(a, mul(b, c)) == mul(mul(a, b), c) : Nat}

def mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      copy2(b, {mul(1n+p, mul(b, c)) == mul(mul(1n+p, b), c) : Nat}, b1 => e1 => b2 => e2 => s12 =>
      copy2(b2, {mul(1n+p, mul(b, c)) == mul(mul(1n+p, b), c) : Nat}, b3 => e3 => b4 => e4 => s34 =>
      copy2(b4, {mul(1n+p, mul(b, c)) == mul(mul(1n+p, b), c) : Nat}, b5 => e5 => b6 => e6 => s56 =>
      copy2(c, {mul(1n+p, mul(b, c)) == mul(mul(1n+p, b), c) : Nat}, cA => ca => cB => cb => sAB =>
      copy2(cB, {mul(1n+p, mul(b, c)) == mul(mul(1n+p, b), c) : Nat}, cC => cc => cD => cd => sCD =>
      %e1 : {mul(1n+p, mul(_, c)) == mul(mul(1n+p, _), c) : Nat}
      %mul_unfold(p, b1) : {mul(1n+p, mul(b1, c)) == mul(_, c) : Nat}
      %s12 : {mul(1n+p, mul(_, c)) == mul(add(_, mul(p, _)), c) : Nat}
      %e3 : {mul(1n+p, mul(b2, c)) == mul(add(_, mul(p, b2)), c) : Nat}
      %ca : {mul(1n+p, mul(b2, _)) == mul(add(b3, mul(p, b2)), _) : Nat}
      %mul_dist(b3, mul(p, b2), cA) : {mul(1n+p, mul(b2, cA)) == _ : Nat}
      %e4 : {mul(1n+p, mul(_, cA)) == add(mul(b3, cA), mul(mul(p, _), cA)) : Nat}
      %e5 : {mul(1n+p, mul(_, cA)) == add(mul(b3, cA), mul(mul(p, _), cA)) : Nat}
      %sAB : {mul(1n+p, mul(b5, _)) == add(mul(b3, _), mul(mul(p, b5), _)) : Nat}
      %cc : {mul(1n+p, mul(b5, cB)) == add(mul(b3, cB), mul(mul(p, b5), _)) : Nat}
      %cd : {mul(1n+p, mul(b5, _)) == add(mul(b3, _), mul(mul(p, b5), cC)) : Nat}
      %mul_assoc(p, b5, cC) : {mul(1n+p, mul(b5, cD)) == add(mul(b3, cD), _) : Nat}
      %s56 : {mul(1n+p, mul(_, cD)) == add(mul(b3, cD), mul(p, mul(_, cC))) : Nat}
      %sCD : {mul(1n+p, mul(b6, cD)) == add(mul(b3, cD), mul(p, mul(b6, _))) : Nat}
      %mul_unfold(p, mul(b6, cD)) : {_ == add(mul(b3, cD), mul(p, mul(b6, cD))) : Nat}
      %s34 : {add(mul(b6, cD), mul(p, mul(b6, cD))) == add(mul(_, cD), mul(p, mul(b6, cD))) : Nat}
      %e6 : {add(mul(b6, cD), mul(p, mul(b6, cD))) == add(mul(_, cD), mul(p, mul(b6, cD))) : Nat}
      {==})))))

# successor never reaches zero, and is injective

assert pred:
  forall n: Nat
  Nat

def pred(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# a Type computed by match, the engine of succ_neq_zero
assert discr:
  forall n: Nat
  Type

def discr(n):
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

assert succ_neq_zero:
  forall -a: Nat
  forall e: {1n+a == 0n : Nat}
  Empty

def succ_neq_zero(a, e):
  %e : discr(_); Unit{}

assert succ_inj:
  forall -a: Nat
  forall -b: Nat
  forall e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  %e : {a == pred(_) : Nat}; {==}

# order is arithmetic: a <= b exactly when b is a plus something.
# le is a computed type: Unit when it holds, Empty when it fails

assert le:
  forall a: Nat
  forall b: Nat
  Type

def le(a, b):
  match a:
    case 0n:
      Unit
    case 1n+ap:
      match b:
        case 0n:
          Empty
        case 1n+bp:
          le(ap, bp)

assert le_diff.con:
  forall -ap: Nat
  forall -bp: Nat
  forall w: (&c: Nat -> {add(ap, c) == bp : Nat})
  exists c: Nat
  {1n+add(ap, c) == 1n+bp : Nat}

assert le_diff:
  forall a: Nat
  forall b: Nat
  forall e: le(a, b)
  (&c: Nat -> {add(a, c) == b : Nat})

def le_diff.con(ap, bp, w):
  (c, prf) = w
  (c, %prf : {1n+add(ap, c) == 1n+_ : Nat}; {==})

def le_diff(a, b, e):
  match a:
    case 0n:
      (b, {==})
    case 1n+ap:
      match b:
        case 0n:
          match e:
        case 1n+bp:
          le_diff.con(ap, bp, le_diff(ap, bp, e))

# the printed answer: base's Nat.show renders the witness and the
# event loop prints it -- the proof produced the value, IO shows it

# a claim instantiates like any def: 21 <= 42, so 42 = 21 + something
assert main.out:
  &c: Nat -> {add(21n, c) == 42n : Nat}

def main.out():
  le_diff(21n, 42n, Unit{})

assert main.fin:
  forall w: (&c: Nat -> {add(21n, c) == 42n : Nat})
  IO(Unit)

assert main:
  IO(Unit)

def main.fin(w):
  (c, e) = w
  s = String.append(Nat.show(c), "n, -}")
  IO.print(String.append("Tuple{", s))

def main():
  main.fin(main.out())
