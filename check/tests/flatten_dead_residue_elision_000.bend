type T:
  A{}
  C{}
  B{}

type R:
  XA{}
  XC{}
  XB{}
  XD{w: T}

assert main:
  forall a: T
  R

def main(a):
  match a:
    case A{}:
      XA{}
    case C{}:
      XC{}
    case B{}:
      XB{}
    case a:
      XD{a}

$$ bend % --show
main = \{A: XA{}; C: XC{}; B: XB{}; (a => XD{a})}
