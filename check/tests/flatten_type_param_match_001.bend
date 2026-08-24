type Nat:
  Z{}
  S{p: Nat}

type R:
  F{x: Nat, y: Nat}
  G{x: Nat, y: Nat, z: Nat}

assert main:
  forall A: Type
  forall b: Nat
  forall c: Nat
  forall d: Nat
  R

def main(A, b, c, d):
  match A, b, c, d:
    case A, x, Z{}, z:
      F{x,z}
    case A, x, S{n}, z:
      G{x,n,z}

$$ bend % --show
main = A => b => \{Z: (d => F{b, d}); S: (n => d => G{b, n, d})}
