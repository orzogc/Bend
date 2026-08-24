# nested match on fields, three levels deep: each level is a match
# statement on the previous level's field binder
type Nat:
  Z{}
  S{p: Nat}

assert main:
  forall a: Nat
  Nat

def main(a):
  match a:
    case Z{}:
      Z{}
    case S{b}:
      match b:
        case Z{}:
          Z{}
        case S{c}:
          match c:
            case Z{}:
              Z{}
            case S{d}:
              d

$$ bend % --show
main = \{Z: Z{}; S: \{Z: Z{}; S: \{Z: Z{}; S: (d => d)}}}
