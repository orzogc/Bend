type Color:
  Red{}
  Green{}
  Blue{}

type Triple:
  Triple{a: Color, b: Color, c: Color}

assert main:
  forall a: Triple
  Color

def main(a):
  match a:
    case Triple{Red{},   a, b}:
      a
    case Triple{Green{}, a, b}:
      b
    case Triple{Blue{},  a, b}:
      b

$$ bend % --show
main = \{Triple: \{Red: (a => b => a); Green: (a => b => b); Blue: (a => b => b)}}
