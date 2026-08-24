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
    case a:
      B{a}

$$ bend % --show
main = \{Z: A{}; (a => B{a})}
