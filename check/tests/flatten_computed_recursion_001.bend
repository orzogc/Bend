# recursion under nested computed matches: each computed decision is
# an applied match-lambda and the shared word rebinds through a +
# local ({m0 : +W}, a local W.copy witness; bend3 contracted it
# freely -- a match-lambda arm binder stays Lone, so the arm spells
# its own Cop)
# ported from bend3: the numeric columns become ctor columns; bend3's
# mutual inner<->main pair folds into ONE def -- inner inlined as a
# match-lambda arm -- whose recursion rides a Nat fuel matched ahead
# of the decisions (the queens shape)
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
      s1 = Equal.cong(W, W, z => S{z}, p, px, pe)
      s2 = Equal.cong(W, W, z => S{z}, p, py, pf)
      ((S{px}, s1), (S{py}, s2))

assert not:
  forall a: Bl
  Bl

def not(a):
  match a:
    case T{}:
      F{}
    case F{}:
      T{}

assert par:
  forall a: W
  Bl

def par(a):
  match a:
    case Z{}:
      T{}
    case S{n}:
      not(par(n))

assert main:
  forall f: Nat
  forall n: W
  W

def main(f, n):
  match f:
    case 0n:
      Z{}
    case 1n+g:
      \{Z: Z{}; S: (m0 => +m = {m0 : +W}; \{T: \{T: S{main(g, m)}; F: Z{}}(par(m)); F: main(g, m)}(par(m)))}(n)
$$ bend % --show
W.copy = \{Z: Tuple{Tuple{Z{}, {==}}, Tuple{Z{}, {==}}}; S: (p => \{Tuple: \{Tuple: (px => pe => \{Tuple: (py => pf => s1 = Equal.cong(W, W, z => S{z}, p, px, pe); s2 = Equal.cong(W, W, z => S{z}, p, py, pf); Tuple{Tuple{S{px}, s1}, Tuple{S{py}, s2}})})}}(W.copy(p)))}
not = \{T: F{}; F: T{}}
par = \{Z: T{}; S: (n => not(par(n)))}
main = \{Zero: (n => Z{}); Succ: (g => n => \{Z: Z{}; S: (m0 => +m = {m0 : +W ~ W.copy}; \{T: \{T: S{main(g, m)}; F: Z{}}(par(m)); F: main(g, m)}(par(m)))}(n))}
