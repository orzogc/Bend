type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{a: Nat, x: Nat, y: Nat}
  C{a: Nat, x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  forall d: Nat
  R

def main(a, b, c, d):
  match a, b, c, d:
    case a, Z{}, c, Z{}:
      A{}
    case a, S{x}, c, y:
      B{a,x,y}
    case a, x, c, y:
      C{a,x,y}

$$ bend % --show
main = a => \{Z: (c => \{Z: A{}; (d => C{a, Z{}, d})}); S: (x => c => d => B{a, x, d}); (b => c => d => C{a, b, d})}
