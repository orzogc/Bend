type Nat:
  Z{}
  S{p: Nat}

type R:
  A{x: Nat, y: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  A{a,b}

$$ bend % --show
main = a => b => A{a, b}
