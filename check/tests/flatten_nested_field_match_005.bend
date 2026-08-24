# deep source pattern PLUS a field-match statement: case S{S{b}} digs two
# levels, then a match statement digs the third
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
    case S{Z{}}:
      Z{}
    case S{S{b}}:
      match b:
        case Z{}:
          Z{}
        case S{c}:
          c

$$ bend % --show
main = \{Z: Z{}; S: \{Z: Z{}; S: \{Z: Z{}; S: (c => c)}}}
