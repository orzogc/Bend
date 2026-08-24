type Nat:
  Z{}
  S{p: Nat}

type MaybeNat:
  None{}
  Some{x: Nat}

assert main:
  forall a: MaybeNat
  MaybeNat

def main(a):
  match a:
    case None{}:
      None{}
    case Some{a}:
      Some{a}

$$ bend % --show
main = \{None: None{}; Some: (a => Some{a})}
