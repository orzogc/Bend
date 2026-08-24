type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat, y: Nat}
  C{x: Nat, y: Nat, z: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  R

def main(a, b, c):
  match a, b, c:
    case Z{}, b, Z{}:
      A{}
    case Z{}, b, S{y}:
      B{y,b}
    case S{x}, b, y:
      C{x,y,b}

$$ bend % --show
main = \{Z: (b => \{Z: A{}; S: (y => B{y, b})}); S: (x => b => c => C{x, c, b})}
