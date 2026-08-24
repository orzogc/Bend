# switch on a computed value with a default row: the rows live in a
# helper def (bend4's match takes bare scrutinees and a match heads a
# def body), the computed call rides its application
# ported from bend3: the numeric domain becomes a ctor word (bend4 has
# no number patterns)
type W:
  Z{}
  S{p: W}

type R:
  R1{}
  RK{k: W}

assert dbl:
  forall x: W
  W

def dbl(x):
  match x:
    case Z{}:
      Z{}
    case S{p}:
      S{S{dbl(p)}}

assert sel:
  forall y: W
  R

def sel(y):
  match y:
    case Z{}:
      R1{}
    case k:
      RK{k}

assert main:
  forall x: W
  R

def main(x):
  sel(dbl(x))
$$ bend % --show
dbl = \{Z: Z{}; S: (p => S{S{dbl(p)}})}
sel = \{Z: R1{}; (y => RK{y})}
main = x => sel(dbl(x))
