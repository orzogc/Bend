type Nat:
  Z{}
  S{p: Nat}

type R:
  A{a: Nat, b: Nat, c: Nat}
  B{a: Nat, b: Nat}
  C{a: Nat, b: Nat}
  D{a: Nat}
  E{a: Nat, b: Nat}
  F{a: Nat}
  G{a: Nat}
  H{}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  R

def main(a, b, c):
  match a, b, c:
    case S{a}, S{b}, S{c}:
      A{a,b,c}
    case S{a}, S{b}, Z{}:
      B{a,b}
    case S{a}, Z{}, S{c}:
      C{a,c}
    case S{a}, Z{}, Z{}:
      D{a}
    case Z{}, S{b}, S{c}:
      E{b,c}
    case Z{}, S{b}, Z{}:
      F{b}
    case Z{}, Z{}, S{c}:
      G{c}
    case Z{}, Z{}, Z{}:
      H{}

$$ bend % --show
main = \{S: (a => \{S: (b => \{S: (c => A{a, b, c}); Z: B{a, b}}); Z: \{S: (c => C{a, c}); Z: D{a}}}); Z: \{S: (b => \{S: (c => E{b, c}); Z: F{b}}); Z: \{S: (c => G{c}); Z: H{}}}}
