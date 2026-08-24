type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat}
  C{x: Nat}
  D{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  R

def main(a, b, c):
  match a, b, c:
    case Z{}, Z{}, c:
      A{}
    case Z{}, x, c:
      B{x}
    case y, Z{}, c:
      C{y}
    case y, x, c:
      D{y, x}

$$ bend % --show
main = \{Z: \{Z: (c => A{}); (b => c => B{b})}; (a => \{Z: (c => C{a}); (b => c => D{a, b})})}
