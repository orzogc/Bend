type Nat:
  Z{}
  S{p: Nat}

type R:
  A{a: Nat}
  B{a: Nat, b: Nat}
  C{a: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case S{a}, S{Z{}}:
      A{a}
    case a, S{b}:
      B{a,b}
    case a, Z{}:
      C{a}

$$ bend % --show
main = \{S: (a => \{S: \{Z: A{a}; (_7 => B{S{a}, _7})}; Z: C{S{a}}}); (a => \{S: (b => B{a, b}); Z: C{a}})}
