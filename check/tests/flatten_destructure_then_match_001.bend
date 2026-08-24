# destructure of a FIELD: a case arm binds a field, a statement then
# destructures it
type Nat:
  Z{}
  S{p: Nat}

type Pair:
  P{a: Nat, b: Nat}

type Box:
  Box{v: Pair}

assert main:
  forall w: Box
  Nat

def main(w):
  match w:
    case Box{v}:
      P{a, b} = v
      a

$$ bend % --show
main = \{Box: \{P: (a => b => a)}}
