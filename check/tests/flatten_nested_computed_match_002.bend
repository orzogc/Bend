# computed scrutinees, nesting included: ctor cases and a nested test
# with a default row (the helper holds it)
# ported from bend3: numeric columns become ctor columns, the n < 5
# comparison becomes a structural test, the shared word wears +
import Base
type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

assert W.copy:
  forall t: W
  Copy(W, t) & Copy(W, t)

def W.copy(t):
  match t:
    case Z{}:
      ((Z{}, {==}), (Z{}, {==}))
    case S{p}:
      ((px, pe), (py, pf)) = W.copy(p)
      s10 = Equal.cong(W, W, z => S{z}, p, px, pe)
      s20 = Equal.cong(W, W, z => S{z}, p, py, pf)
      ((S{px}, s10), (S{py}, s20))

type R:
  K1{}
  K500{}
  K50{}

assert not:
  forall a: Bl
  Bl

def not(a):
  match a:
    case T{}:
      F{}
    case F{}:
      T{}

assert odd:
  forall a: W
  Bl

def odd(a):
  match a:
    case Z{}:
      F{}
    case S{n}:
      not(odd(n))

assert small:
  forall x: W
  Bl

def small(x):
  match x:
    case Z{}:
      T{}
    case k:
      F{}

assert main:
  forall +n: +W
  R

def main(n):
  \{T: K1{}; F: \{T: K50{}; F: K500{}}(small(n))}(odd(n))
$$ bend % --show
W.copy = \{Z: Tuple{Tuple{Z{}, {==}}, Tuple{Z{}, {==}}}; S: (p => \{Tuple: \{Tuple: (px => pe => \{Tuple: (py => pf => s10 = Equal.cong(W, W, z => S{z}, p, px, pe); s20 = Equal.cong(W, W, z => S{z}, p, py, pf); Tuple{Tuple{S{px}, s10}, Tuple{S{py}, s20}})})}}(W.copy(p)))}
not = \{T: F{}; F: T{}}
odd = \{Z: F{}; S: (n => not(odd(n)))}
small = \{Z: T{}; (x => F{})}
main = n => \{T: K1{}; F: \{T: K50{}; F: K500{}}(small(n))}(odd(n))
