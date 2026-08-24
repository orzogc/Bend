type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat}

assert main:
  forall a: Nat
  R

def main(a):
  match a:
    case Z{}:
      A{}
    case S{a}:
      B{a}

$$ bend % --show
main = \{Z: A{}; S: (a => B{a})}
