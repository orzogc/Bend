# mul_comm, complete, over a local Nat -- the goal-ladder base
# (proof_goal_ladder_state_000+ pin this proof's intermediate states):
# mul_zero, the add_swap stepping-stone, mul_succ, then the two-rewrite
# close.
# ported from bend3: every rewrite carries an explicit motive; add_succ
# and mul_succ are stated with the term each rewrite eliminates on the
# right; the double spends ride +N Cop binders over N.copy
import Base
type N:
  Z{}
  S{p: N}

assert N.copy:
  forall t: N
  Copy(N, t) & Copy(N, t)

def N.copy(t):
  match t:
    case Z{}:
      ((Z{}, {==}), (Z{}, {==}))
    case S{p}:
      ((px, pe), (py, pf)) = N.copy(p)
      s10 = Equal.cong(N, N, z => S{z}, p, px, pe)
      s20 = Equal.cong(N, N, z => S{z}, p, py, pf)
      ((S{px}, s10), (S{py}, s20))

assert add:
  forall a: N
  forall b: N
  N

def add(a, b):
  match a:
    case Z{}:
      b
    case S{p}:
      S{add(p, b)}

assert mul:
  forall a: N
  forall +b: +N
  N

def mul(a, b):
  match a:
    case Z{}:
      Z{}
    case S{p}:
      add(b, mul(p, b))

assert add_succ:
  forall a: N
  forall -b: N
  {S{add(a, b)} == add(a, S{b}) : N}

def add_succ(a, b):
  match a:
    case Z{}:
      {==}
    case S{p}:
      %add_succ(p, b) : {S{S{add(p, b)}} == S{_} : N}
      {==}

assert add_swap:
  forall +x: +N
  forall +y: +N
  forall +z: +N
  {add(x, add(y, z)) == add(y, add(x, z)) : N}

def add_swap(x, y, z):
  match x:
    case Z{}:
      {==}
    case S{q}:
      %add_succ(y, add(q, z)) : {S{add(q, add(y, z))} == _ : N}
      %add_swap(q, y, z) : {S{add(q, add(y, z))} == S{_} : N}
      {==}

assert mul_zero:
  forall a: N
  {mul(a, Z{}) == Z{} : N}

def mul_zero(a):
  match a:
    case Z{}:
      {==}
    case S{p}:
      mul_zero(p)

assert mul_succ:
  forall +a: +N
  forall +b: +N
  {add(a, mul(a, b)) == mul(a, S{b}) : N}

def mul_succ(a, b):
  match a:
    case Z{}:
      {==}
    case S{p}:
      %mul_succ(p, b) : {S{add(p, add(b, mul(p, b)))} == S{add(b, _)} : N}
      %add_swap(p, b, mul(p, b)) : {S{add(p, add(b, mul(p, b)))} == S{_} : N}
      {==}

assert mul_comm:
  forall +a: +N
  forall +b: +N
  {mul(a, b) == mul(b, a) : N}

def mul_comm(a, b):
  match a:
    case Z{}:
      %mul_zero(b) : {_ == mul(b, Z{}) : N}
      {==}
    case S{p}:
      %mul_succ(b, p) : {add(b, mul(p, b)) == _ : N}
      %mul_comm(p, b) : {add(b, mul(p, b)) == add(b, _) : N}
      {==}

assert main:
  {mul(S{S{Z{}}}, S{S{S{Z{}}}}) == mul(S{S{S{Z{}}}}, S{S{Z{}}}) : N}

def main(): mul_comm(S{S{Z{}}}, S{S{S{Z{}}}})

$$ bend %
{==}
