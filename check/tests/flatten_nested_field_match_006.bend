# multi-column outer, field-match inner: both params eliminate as columns
# and the inner statement refines the second's field
type Nat:
  Z{}
  S{p: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  Nat

def main(a, b):
  match a, b:
    case Z{}, y:
      y
    case S{x}, Z{}:
      x
    case S{x}, S{y}:
      match y:
        case Z{}:
          x
        case S{p}:
          p

$$ bend % --show
main = \{Z: (b => b); S: (x => \{Z: x; S: \{Z: x; S: (p => p)}})}
