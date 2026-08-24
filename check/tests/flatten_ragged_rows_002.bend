# ragged matrix over three columns: the trailing catch-all row rides
# and dominates where it leads; every row is live.
type Nat:
  Z{}
  S{p: Nat}

type R:
  A{a: Nat, b: Nat, c: Nat}
  B{a: Nat, b: Nat, c: Nat}
  C{a: Nat, b: Nat}
  D{a: Nat, b: Nat, c: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  forall c: Nat
  R

def main(a, b, c):
  match a, b, c:
    case S{a}, S{b}, S{c}:
      A{a,b,c}
    case S{a}, S{b}, c:
      B{a,b,c}
    case S{a}, b, Z{}:
      C{a,b}
    case a, b, c:
      D{a,b,c}

$$ bend % --show
main = \{S: (a => \{S: (b => \{S: (c => A{a, b, c}); Z: B{a, b, Z{}}; (c => B{a, b, c})}); (b => \{Z: C{a, b}; (c => D{S{a}, b, c})})}); (a => b => c => D{a, b, c})}
