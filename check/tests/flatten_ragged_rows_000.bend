# ragged matrices are legal: default rows above rigid rows ride into
# the groups they reach, first-match order; every row here is live.
type Nat:
  Z{}
  S{p: Nat}

type R:
  A{a: Nat, b: Nat}
  B{a: Nat, b: Nat}
  C{a: Nat}
  D{a: Nat, b: Nat}
  E{a: Nat, b: Nat}
  F{a: Nat}

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
    case a, S{b}:
      E{a,b}
    case a, Z{}:
      F{a}

$$ bend % --show
main = \{S: \{S: (a => \{S: \{S: (b => A{a, b}); (_14 => B{a, _14})}; Z: C{S{a}}; (b => D{S{a}, b})}); (_12 => \{Z: C{_12}; S: (b => D{_12, S{b}}); (b => D{_12, b})})}; (a => \{S: (b => E{a, b}); Z: F{a}})}
