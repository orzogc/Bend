# computed scrutinee, ref call: the group is stuck on f(n) and the
# application shows -- bend4 spells it as the applied match-lambda
# ported from bend3: literal arm values become ctors
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
  \{T: S{Z{}}; F: Z{}}(f(n))
$$ bend % --show
f = \{Zn: T{}; Sn: (p => F{})}
main = n => \{T: S{Z{}}; F: Z{}}(f(n))
