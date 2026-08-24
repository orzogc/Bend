type Nat:
  Z{}
  S{p: Nat}

type R:
  A{a: Nat, b: Nat}
  B{a: Nat}
  C{b: Nat}
  D{}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case S{a}, S{b}:
      A{a,b}
    case S{a}, Z{}:
      B{a}
    case Z{}, S{b}:
      C{b}
    case Z{}, Z{}:
      D{}

$$ bend % --show
main = \{S: (a => \{S: (b => A{a, b}); Z: B{a}}); Z: \{S: (b => C{b}); Z: D{}}}
