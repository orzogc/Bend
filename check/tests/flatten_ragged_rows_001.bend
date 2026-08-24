# ragged matrix: a leading `Z{} b` default-b row closes its branch
# without touching column b (dominance), the rigid rows drive the rest.
type Nat:
  Z{}
  S{p: Nat}

type R:
  A{b: Nat}
  B{a: Nat, b: Nat}
  C{a: Nat}

assert main:
  forall a: Nat
  forall b: Nat
  R

def main(a, b):
  match a, b:
    case Z{}, b:
      A{b}
    case a, S{b}:
      B{a,b}
    case a, Z{}:
      C{a}

$$ bend % --show
main = \{Z: \{S: (b => A{S{b}}); Z: A{Z{}}; (b => A{b})}; (a => \{S: (b => B{a, b}); Z: C{a}})}
