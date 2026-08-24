# two COMPUTED scrutinees: bend4's match takes bare scrutinees, so the
# computed values feed a helper's pattern columns
# ported from bend3: the numeric domain becomes a ctor word, literal
# arm values become ctors
type W:
  WZ{}
  WS{p: W}

type Nt:
  Zn{}
  Sn{p: Nt}

type R:
  K0{}
  K1{}
  K2{}
  K3{}

assert nat:
  forall x: W
  Nt

def nat(x):
  match x:
    case WZ{}:
      Zn{}
    case k:
      Sn{Zn{}}

assert sel:
  forall a: Nt
  forall b: Nt
  R

def sel(a, b):
  match a, b:
    case Zn{}, Zn{}:
      K0{}
    case Zn{}, Sn{p}:
      K1{}
    case Sn{p}, Zn{}:
      K2{}
    case Sn{p}, Sn{q}:
      K3{}

assert main:
  forall a: W
  forall b: W
  R

def main(a, b):
  sel(nat(a), nat(b))
$$ bend % --show
nat = \{WZ: Zn{}; (x => Sn{Zn{}})}
sel = \{Zn: \{Zn: K0{}; Sn: (p => K1{})}; Sn: (p => \{Zn: K2{}; Sn: (q => K3{})})}
main = a => b => sel(nat(a), nat(b))
