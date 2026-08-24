#[halts]
# recursion through a computed match: the decision factors into helper
# defs (bend4's idiom: a match heads a def body; a computed match is
# the applied match-lambda), and the kept scrutinee wears +
# ported from bend3: literal arm values become ctors, mutual recursion
# rides #[halts]
type Nt:
  Zn{}
  Sn{p: Nt}

type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

assert big:
  forall a: Nt
  Bl

def big(a):
  match a:
    case Zn{}:
      F{}
    case Sn{Zn{}}:
      F{}
    case Sn{Sn{p}}:
      T{}

assert deep:
  forall m: Nt
  W

def deep(m):
  match m:
    case Sn{Sn{p}}:
      S{S{main(p)}}
    case Sn{Zn{}}:
      S{Z{}}
    case Zn{}:
      S{Z{}}

assert main:
  forall +n: Nt
  W

def main(n):
  \{T: deep(n); F: Z{}}(big(n))
$$ bend % --show
big = \{Zn: F{}; Sn: \{Zn: F{}; Sn: (p => T{})}}
deep = \{Sn: \{Sn: (p => S{S{main(p)}}); Zn: S{Z{}}}; Zn: S{Z{}}}
main = n => \{T: deep(n); F: Z{}}(big(n))
