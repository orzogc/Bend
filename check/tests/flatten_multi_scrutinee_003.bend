type Nat:
  Z{}
  S{p: Nat}

type R:
  A{a: Nat, b: Nat}
  B{a: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case a, S{b}:
      A{a,b}
    case a, Z{}:
      B{a}

$$ bend % --show
main = a => \{S: (b => A{a, b}); Z: B{a}}
