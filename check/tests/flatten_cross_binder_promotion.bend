# cross-binder promotion: a multi-scrutinee group where x's pattern
# rebinds the OTHER scrutinee's name y -- both columns still consume
# (the shadowed layout y is renamed away, the case's y wins)
type Nat:
  Z{}
  S{p: Nat}
type Pr:
  P{a: Nat, b: Nat}

assert main:
  forall x: Pr
  forall y: Nat
  Nat

def main(x, y):
  match x, y:
    case P{y, z}, S{q}:
      y
    case P{y, z}, Z{}:
      z

$$ bend % --show
main = \{P: (y => z => \{S: (q => y); Z: z})}
