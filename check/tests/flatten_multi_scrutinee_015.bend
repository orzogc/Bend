# ported from bend3: the U32 column becomes a ctor word
type Nat:
  Z{}
  S{p: Nat}

type MaybeNat:
  None{}
  Some{x: Nat}

type W:
  WZ{}
  WS{p: W}

assert main:
  forall a: MaybeNat
  forall b: W
  MaybeNat

def main(a, b):
  match a, b:
    case None{}, a:
      None{}
    case Some{a}, b:
      Some{a}
$$ bend % --show
main = \{None: (b => None{}); Some: (a => b => Some{a})}
