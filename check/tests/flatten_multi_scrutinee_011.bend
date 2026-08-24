type Nat:
  Z{}
  S{p: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  Nat

def main(a, b):
  match a, b:
    case Z{}, a:
      a
    case S{a}, b:
      a

$$ bend % --show
main = \{Z: (b => b); S: (a => b => a)}
