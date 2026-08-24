type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat}
  C{x: Nat}

assert main:
  forall a: Nat
  R

def main(a):
  match a:
    case Z{}:
      A{}
    case S{S{a}}:
      C{a}
    case S{a}:
      B{a}

$$ bend % --show
main = \{Z: A{}; S: \{S: (a => C{a}); (_3 => B{_3})}}
