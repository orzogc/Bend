# a literal row and a default row
# ported from bend3: the numeric column becomes a ctor column and the
# literal results become ctors (bend4 has no number patterns)
type W:
  Z{}
  S{p: W}

type R:
  R1{}
  R2{}

assert main:
  forall a: W
  R

def main(a):
  match a:
    case Z{}:
      R1{}
    case n:
      R2{}
$$ bend % --show
main = \{Z: R1{}; (a => R2{})}
