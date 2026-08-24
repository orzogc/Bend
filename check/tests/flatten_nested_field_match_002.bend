# nested field match with an inner DEFAULT arm: the catch-all closes the
# inner level, binding the field's value
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
        case S{c}:
          c
        case w:
          S{w}

$$ bend % --show
main = \{Z: Z{}; S: \{S: (c => c); (b => S{b})}}
