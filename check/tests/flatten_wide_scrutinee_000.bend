type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat, y: Nat}
  C{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  forall d: Nat
  R

def main(a, b, c, d):
  match a, b, c, d:
    case Z{}, b, c, Z{}:
      A{}
    case S{x}, b, c, y:
      B{x,y}
    case x, b, c, y:
      C{x,y}

$$ bend % --show
main = \{Z: (b => c => \{Z: A{}; (d => C{Z{}, d})}); S: (x => b => c => d => B{x, d}); (a => b => c => d => C{a, d})}
