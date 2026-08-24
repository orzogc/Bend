type Nat:
  Z{}
  S{p: Nat}

type R:
  A{}
  B{x: Nat}
  C{x: Nat}

assert main:
  forall a: Nat
  R

def main(a):
  match a:
    case Z{}:
      A{}
    case S{S{S{a}}}:
      B{a}
    case S{a}:
      C{a}

$$ bend % --show
main = \{Z: A{}; S: \{S: \{S: (a => B{a}); (_4 => C{S{_4}})}; (_3 => C{_3})}}
