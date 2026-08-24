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
    case Z{}, S{x}, c:
      B{x}
    case S{x}, Z{}, c:
      C{x}
    case y, z, c:
      D{y, z}

$$ bend % --show
main = \{Z: \{Z: (c => A{}); S: (x => c => B{x}); (b => c => D{Z{}, b})}; S: (x => \{Z: (c => C{x}); (b => c => D{S{x}, b})}); (a => b => c => D{a, b})}
