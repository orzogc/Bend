# multi-scrutinee match: two pattern-column scrutinees, all four case
# combos
# ported from bend3: literal arm values become ctors
type Bit:
  O{}
  I{}

type R:
  K0{}
  K1{}
  K2{}
  K3{}

assert main:
  forall a: Bit
  forall b: Bit
  R

def main(a, b):
  match a, b:
    case O{}, O{}:
      K0{}
    case O{}, I{}:
      K1{}
    case I{}, O{}:
      K2{}
    case I{}, I{}:
      K3{}
$$ bend % --show
main = \{O: \{O: K0{}; I: K1{}}; I: \{O: K2{}; I: K3{}}}
