# nested match on a pattern FIELD: the inner match statement refines the
# field binder in place -- a direct two-level case tree, no aux
type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat}

assert main:
  forall a: Nat
  R

def main(a):
  match a:
    case Z{}:
      A{}
    case S{b}:
      match b:
        case Z{}:
          A{}
        case S{c}:
          B{c}

$$ bend % --show
main = \{Z: A{}; S: \{Z: A{}; S: (c => B{c})}}
