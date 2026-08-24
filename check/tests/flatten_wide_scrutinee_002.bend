type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat, y: Nat, z: Nat}
  C{x: Nat, y: Nat, z: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  forall d: Nat
  forall e: Nat
  R

def main(a, b, c, d, e):
  match a, b, c, d, e:
    case Z{}, b, Z{}, d, Z{}:
      A{}
    case S{x}, b, y, d, S{z}:
      B{x,y,z}
    case x, b, y, d, z:
      C{x,y,z}

$$ bend % --show
main = \{Z: (b => \{Z: (d => \{Z: A{}; (e => C{Z{}, Z{}, e})}); (c => d => e => C{Z{}, c, e})}); S: (x => b => c => d => \{S: (z => B{x, c, z}); (e => C{S{x}, c, e})}); (a => b => c => d => e => C{a, c, e})}
