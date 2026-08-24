type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{a: Nat, b: Nat, c: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  R

def main(a, b, c):
  match a, b, c:
    case Z{}, a, b:
      A{}
    case S{a}, b, c:
      B{S{a}, b, c}

$$ bend % --show
main = \{Z: (b => c => A{}); S: (a => b => c => B{S{a}, b, c})}
