#[halts]
# recursion under nested computed matches: each computed decision is an
# applied match-lambda, the shared word wears + (bend3 contracted it
# freely), and the cycle rides #[halts]
# ported from bend3: the numeric columns become ctor columns
type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

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

assert inner:
  forall +n: W
  W

def inner(n):
  \{T: S{main(n)}; F: Z{}}(par(n))

assert main:
  forall +n: W
  W

def main(n):
  match n:
    case Z{}:
      Z{}
    case S{m}:
      \{T: inner(m); F: main(m)}(par(m))
$$ bend % --show
not = \{T: F{}; F: T{}}
par = \{Z: T{}; S: (n => not(par(n)))}
inner = n => \{T: S{main(n)}; F: Z{}}(par(n))
main = \{Z: Z{}; S: (m => \{T: inner(m); F: main(m)}(par(m)))}
