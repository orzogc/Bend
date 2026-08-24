type Nat:
  Z{}
  S{p: Nat}

type R:
  A{a: Nat, b: Nat}
  B{a: Nat, b: Nat}
  C{a: Nat}
  D{a: Nat, b: Nat}
  E{a: Nat, b: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case S{S{a}}, S{S{b}}:
      A{a,b}
    case S{S{a}}, S{b}:
      B{a,b}
    case S{a}, Z{}:
      C{a}
    case S{a}, b:
      D{a,b}
    case a, b:
      E{a,b}

$$ bend % --show
main = \{S: \{S: (a => \{S: \{S: (b => A{a, b}); (_13 => B{a, _13})}; Z: C{S{a}}; (b => D{S{a}, b})}); (_11 => \{Z: C{_11}; (b => D{_11, b})})}; (a => b => E{a, b})}
