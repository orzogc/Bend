# three scrutinees mixing pattern columns and a COMPUTED middle; bend4's
# match takes bare scrutinees, so the computed value feeds a helper's
# var column and the ctor rows flatten there
# ported from bend3: literal arm values become ctors
type Bit:
  O{}
  I{}

type R:
  K0{}
  K1{}
  K2{}
  K3{}
  K4{}
  K5{}
  K6{}
  K7{}

assert flip:
  forall b: Bit
  Bit

def flip(b):
  match b:
    case O{}:
      I{}
    case I{}:
      O{}

assert sel:
  forall a: Bit
  forall fb: Bit
  forall c: Bit
  R

def sel(a, fb, c):
  match a, fb, c:
    case O{}, O{}, O{}:
      K0{}
    case O{}, O{}, I{}:
      K1{}
    case O{}, I{}, O{}:
      K2{}
    case O{}, I{}, I{}:
      K3{}
    case I{}, O{}, O{}:
      K4{}
    case I{}, O{}, I{}:
      K5{}
    case I{}, I{}, O{}:
      K6{}
    case I{}, I{}, I{}:
      K7{}

assert main:
  forall a: Bit
  forall b: Bit
  forall c: Bit
  R

def main(a, b, c):
  sel(a, flip(b), c)
$$ bend % --show
flip = \{O: I{}; I: O{}}
sel = \{O: \{O: \{O: K0{}; I: K1{}}; I: \{O: K2{}; I: K3{}}}; I: \{O: \{O: K4{}; I: K5{}}; I: \{O: K6{}; I: K7{}}}}
main = a => b => c => sel(a, flip(b), c)
