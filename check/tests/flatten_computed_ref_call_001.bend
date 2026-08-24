# bend3 pinned that a LET-BOUND call result matches like the computed
# call itself; bend4 agrees: the let variable's match flattens to the
# match-lambda applied to the variable under the let
type Nt:
  Zn{}
  Sn{p: Nt}

type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

assert f:
  forall n: Nt
  Bl

def f(n):
  match n:
    case Zn{}:
      T{}
    case Sn{p}:
      F{}

assert main:
  forall n: Nt
  W

def main(n):
  w = f(n)
  match w:
    case T{}:
      S{Z{}}
    case F{}:
      Z{}
$$ bend % --show
f = \{Zn: T{}; Sn: (p => F{})}
main = n => w = f(n); \{T: S{Z{}}; F: Z{}}(w)
