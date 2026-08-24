# nested computed matches (a computed scrutinee per level): bend4 spells
# each as the applied match-lambda; the shared word wears +
# ported from bend3: numeric columns become ctor columns, literal arm
# values become ctors
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
  K2{}
  K3{}

assert pos:
  forall a: W
  Bl

def pos(a):
  match a:
    case Z{}:
      F{}
    case n:
      T{}

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

assert main:
  forall +n: +W
  R

def main(n):
  \{T: \{T: K1{}; F: K2{}}(odd(n)); F: K3{}}(pos(n))
$$ bend % --show
W.copy = \{Z: Tuple{Tuple{Z{}, {==}}, Tuple{Z{}, {==}}}; S: (p => \{Tuple: \{Tuple: (px => pe => \{Tuple: (py => pf => s10 = Equal.cong(W, W, z => S{z}, p, px, pe); s20 = Equal.cong(W, W, z => S{z}, p, py, pf); Tuple{Tuple{S{px}, s10}, Tuple{S{py}, s20}})})}}(W.copy(p)))}
pos = \{Z: F{}; (a => T{})}
not = \{T: F{}; F: T{}}
odd = \{Z: F{}; S: (n => not(odd(n)))}
main = n => \{T: \{T: K1{}; F: K2{}}(odd(n)); F: K3{}}(pos(n))
