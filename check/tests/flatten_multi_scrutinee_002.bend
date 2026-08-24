type Nat:
  Z{}
  S{p: Nat}

type R:
  A{x: Nat, y: Nat}
  B{x: Nat}
  C{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case S{a}, S{b}:
      A{a,b}
    case Z{}, b:
      B{b}
    case a, b:
      C{a,b}

$$ bend % --show
main = \{S: (a => \{S: (b => A{a, b}); (b => C{S{a}, b})}); Z: (b => B{b}); (a => b => C{a, b})}
