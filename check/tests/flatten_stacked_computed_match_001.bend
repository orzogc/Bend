# three stacked computed scrutinees: the computed values feed a
# helper's columns in order
# ported from bend3: literal arm values become ctors
type Bl:
  T{}
  F{}

type R:
  K1{}
  K2{}
  K3{}
  K4{}

assert not:
  forall a: Bl
  Bl

def not(a):
  match a:
    case T{}:
      F{}
    case F{}:
      T{}

assert sel:
  forall a: Bl
  forall b: Bl
  forall c: Bl
  R

def sel(a, b, c):
  match a, b, c:
    case T{}, T{}, x:
      K1{}
    case T{}, F{}, x:
      K2{}
    case F{}, x, T{}:
      K3{}
    case F{}, x, F{}:
      K4{}

assert main:
  forall a: Bl
  forall b: Bl
  forall c: Bl
  R

def main(a, b, c):
  sel(not(a), not(b), not(c))
$$ bend % --show
not = \{T: F{}; F: T{}}
sel = \{T: \{T: (c => K1{}); F: (c => K2{})}; F: (b => \{T: K3{}; F: K4{}})}
main = a => b => c => sel(not(a), not(b), not(c))
