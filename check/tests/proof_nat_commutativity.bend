# add_comm over a local Nat: m is spent twice -- once inside add_succ's
# live position, once by the IH.
# ported from bend3: the double spend bend3 allowed on any Data binder
# is bend4's +m Cop binder over the local N.copy witness; add_succ is
# stated with the term each rewrite eliminates on the RIGHT, since a
# bend4 rewrite folds the right endpoint back into the left

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
  forall n: N
  forall m: N
  N

def add(n, m):
  match n:
    case Z{}:
      m
    case S{k}:
      S{add(k, m)}

assert add_zero:
  forall n: N
  {add(n, Z{}) == n : N}

def add_zero(n):
  match n:
    case Z{}:
      {==}
    case S{k}:
      %add_zero(k) : {S{add(k, Z{})} == S{_} : N}; {==}

assert add_succ:
  forall n: N
  forall -m: N
  {S{add(n, m)} == add(n, S{m}) : N}

def add_succ(n, m):
  match n:
    case Z{}:
      {==}
    case S{k}:
      %add_succ(k, m) : {S{S{add(k, m)}} == S{_} : N}; {==}

assert add_comm:
  forall n: N
  forall +m: +N
  {add(n, m) == add(m, n) : N}

def add_comm(n, m):
  match n:
    case Z{}:
      %add_zero(m) : {_ == add(m, Z{}) : N}; {==}
    case S{k}:
      %add_succ(m, k) : {S{add(k, m)} == _ : N}
      %add_comm(k, m) : {S{add(k, m)} == S{_} : N}
      {==}

assert main:
  {add(S{S{Z{}}}, S{Z{}}) == add(S{Z{}}, S{S{Z{}}}) : N}

def main(): add_comm(S{S{Z{}}}, S{Z{}})

$$ bend %
{==}
