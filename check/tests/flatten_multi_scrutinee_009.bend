type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case Z{}, Z{}:
      A{}
    case x, y:
      B{x, y}

$$ bend % --show
main = \{Z: \{Z: A{}; (b => B{Z{}, b})}; (a => b => B{a, b})}
