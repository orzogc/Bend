type Nat:
  Z{}
  S{p: Nat}

type R:
  A{x: Nat}
  B{x: Nat, y: Nat}
  C{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case S{a}, Z{}:
      A{a}
    case S{a}, b:
      B{a,b}
    case a, b:
      C{a,b}

$$ bend % --show
main = \{S: (a => \{Z: A{a}; (b => B{a, b})}); (a => b => C{a, b})}
