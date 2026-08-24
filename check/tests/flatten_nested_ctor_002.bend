type Bit:
  Zer{}
  One{}

type BitPair:
  Pair{f: Bit, s: Bit}

assert main:
  forall a: BitPair
  Bit

def main(a):
  match a:
    case Pair{Zer{}, a}:
      a
    case Pair{One{}, a}:
      a

$$ bend % --show
main = \{Pair: \{Zer: (a => a); One: (a => a)}}
