# a literal row and a default row over three columns
# ported from bend3: the numeric column becomes a ctor column and the
# arm values become ctor builds (bend4 has no number patterns)
type W:
  Z{}
  S{p: W}

type R:
  RA{a: W, b: W}
  RN{n: W}

assert main:
  forall a: W
  forall b: W
  forall c: W
  R

def main(a, b, c):
  match a, b, c:
    case Z{}, a, b:
      RA{a, b}
    case n, a, b:
      RN{n}
$$ bend % --show
main = \{Z: (b => c => RA{b, c}); (a => b => c => RN{a})}
