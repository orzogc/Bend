type Nat:
  Z{}
  S{p: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  Nat

def main(a, b, c):
  match a, b, c:
    case Z{}, a, b:
      a
    case S{a}, b, c:
      b

$$ bend % --show
main = \{Z: (b => c => b); S: (a => b => c => b)}
