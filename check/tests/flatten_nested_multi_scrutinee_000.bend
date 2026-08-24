type Nat:
  Z{}
  S{p: Nat}

type R:
  A{x: Nat, y: Nat}
  B{x: Nat, y: Nat}
  C{x: Nat}
  D{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case S{a}, S{S{b}}:
      A{a,b}
    case S{a}, S{b}:
      B{a,b}
    case S{a}, Z{}:
      C{a}
    case d, e:
      D{d,e}

$$ bend % --show
main = \{S: (a => \{S: \{S: (b => A{a, b}); (_12 => B{a, _12})}; Z: C{a}; (b => D{S{a}, b})}); (a => b => D{a, b})}
