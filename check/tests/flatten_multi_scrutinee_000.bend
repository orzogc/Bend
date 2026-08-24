type Nat:
  Z{}
  S{p: Nat}

type R:
  A{x: Nat}
  B{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case Z{}, b:
      A{b}
    case a, b:
      B{a,b}

$$ bend % --show
main = \{Z: (b => A{b}); (a => b => B{a, b})}
