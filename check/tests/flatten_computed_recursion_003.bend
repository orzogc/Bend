# self recursion into a datatype group (fold-then-inspect): the
# computed decision is the applied match-lambda over the recursive call
type Nt:
  Zn{}
  Sn{p: Nt}

type Bl:
  T{}
  F{}

assert main:
  forall n: Nt
  Bl

def main(n):
  match n:
    case Zn{}:
      T{}
    case Sn{p}:
      \{T: F{}; F: T{}}(main(p))
$$ bend % --show
main = \{Zn: T{}; Sn: (p => \{T: F{}; F: T{}}(main(p)))}
