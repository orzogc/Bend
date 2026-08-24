# a computed match nested under a constructor case (field types come
# from the ADT): the inner decision is the applied match-lambda
# ported from bend3: literal arm values become ctors
type Nt:
  Zn{}
  Sn{p: Nt}

type Bl:
  T{}
  F{}

type R:
  K5{}
  K6{}
  K7{}

assert zro:
  forall a: Nt
  Bl

def zro(a):
  match a:
    case Zn{}:
      T{}
    case Sn{p}:
      F{}

assert main:
  forall n: Nt
  R

def main(n):
  match n:
    case Zn{}:
      K5{}
    case Sn{p}:
      \{T: K6{}; F: K7{}}(zro(p))
$$ bend % --show
zro = \{Zn: T{}; Sn: (p => F{})}
main = \{Zn: K5{}; Sn: (p => \{T: K6{}; F: K7{}}(zro(p)))}
