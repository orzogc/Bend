# switch with a default binder over the miss value
# ported from bend3: the numeric column becomes a ctor column; the
# share-rebound doubled use has no affine spelling, the default arm
# carries its binder once
type W:
  Z{}
  S{p: W}

type R:
  RZ{}
  RD{n: W}

assert main:
  forall x: W
  R

def main(x):
  match x:
    case Z{}:
      RZ{}
    case n:
      RD{n}
$$ bend % --show
main = \{Z: RZ{}; (x => RD{x})}
