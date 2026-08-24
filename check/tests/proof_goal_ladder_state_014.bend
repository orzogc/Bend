# goal ladder, add_comm S-arm state 1 (after the add_succ rewrite).
# ported from bend3: the ladder rides the ported bend4 development, so
# the pinned page is bend4's own goal at the same proof state
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

assert add_zero:
  forall a: N
  {add(a, Z{}) == a : N}

def add_zero(a):
  match a:
    case Z{}:
      {==}
    case S{p}:
      %add_zero(p) : {S{add(p, Z{})} == S{_} : N}
      {==}

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

assert add_comm:
  forall +a: +N
  forall +b: +N
  {add(a, b) == add(b, a) : N}

def add_comm(a, b):
  match a:
    case Z{}:
      %add_zero(b) : {_ == add(b, Z{}) : N}
      {==}
    case S{p}:
      %add_succ(b, p) : {S{add(p, b)} == _ : N}
      Type

$$ bend %
Error:
- expected : {S{add(p, b)} == S{add(b, p)} : N}
- observed : Type
Context:
- p : N
- b : +N ~ N.copy
Location: add_comm
71 |       %add_succ(b, p) : {S{add(p, b)} == _ : N}
72>|       Type
73 |
