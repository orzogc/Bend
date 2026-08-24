type Nat:
  Z{}
  S{p: Nat}

type R:
  A{x: Nat, y: Nat}
  B{x: Nat, y: Nat, z: Nat}
  C{x: Nat, y: Nat, z: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  forall d: Nat
  R

def main(a, b, c, d):
  match a, b, c, d:
    case Z{}, b, c, Z{}:
      A{b,c}
    case Z{}, b, c, S{y}:
      B{y,b,c}
    case S{x}, b, c, y:
      C{x,y,c}

$$ bend % --show
main = \{Z: (b => c => \{Z: A{b, c}; S: (y => B{y, b, c})}); S: (x => b => c => d => C{x, d, c})}
