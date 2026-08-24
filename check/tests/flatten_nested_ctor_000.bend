type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{}
  C{x: Nat}

assert main:
  forall a: Nat
  R

def main(a):
  match a:
    case Z{}:
      A{}
    case S{Z{}}:
      B{}
    case S{S{a}}:
      C{a}

$$ bend % --show
main = \{Z: A{}; S: \{Z: B{}; S: (a => C{a})}}
