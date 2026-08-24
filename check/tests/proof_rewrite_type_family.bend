# rewriting a NON-equation goal: the target is a computed Type-family
# (IsEven of a stuck add), stepped by a lemma rewrite until the family
# computes and the IH's evidence fits.
# ported from bend3: add_succ is stated with the eliminated term on the
# right; the arm spends p twice (lemma and IH), so it rebinds a +N Cop
# local over the local N.copy witness
import Base
type Uni:
  U{}
type Emp:

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

assert IsEven:
  forall n: N
  Type

def IsEven(n):
  match n:
    case Z{}:
      Uni
    case S{Z{}}:
      Emp
    case S{S{p}}:
      IsEven(p)

assert even_dbl:
  forall n: N
  IsEven(add(n, n))

def even_dbl(n):
  match n:
    case Z{}:
      U{}
    case S{p}:
      +q = {p : +N}
      %add_succ(q, q) : IsEven(S{_})
      even_dbl(q)

$$ bend %
