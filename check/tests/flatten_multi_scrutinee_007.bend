type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  R

def main(a, b, c):
  match a, b, c:
    case Z{}, b, Z{}:
      A{}
    case a, b, c:
      B{a,c}

$$ bend % --show
main = \{Z: (b => \{Z: A{}; (c => B{Z{}, c})}); (a => b => c => B{a, c})}
