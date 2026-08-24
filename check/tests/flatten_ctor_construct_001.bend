type Nat:
  Z{}
  S{p: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  Nat

def main(a, b):
  a

$$ bend % --show
main = a => b => a
