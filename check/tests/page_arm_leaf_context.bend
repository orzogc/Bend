# an arm's error page shows the leaf context: n, the hypothesis h,
# then the field p
# ported from bend3: bend4's computed match never specializes
# hypotheses, so h stays at the frozen {dbl(n) == MZ{}} spelling (in
# bend3 it showed the specialized {S{p} == 0n})
import Base
type MNat:
  MZ{}
  MS{p: MNat}

assert dbl:
  forall n: MNat
  MNat

def dbl(n):
  match n:
    case MZ{}:
      MZ{}
    case MS{p}:
      MS{MS{dbl(p)}}

assert use:
  forall n: MNat
  forall h: {dbl(n) == MZ{} : MNat}
  U32

def use(n, h):
  match dbl(n):
    case MZ{}:
      b = h
      0
    case MS{p}:
      p

$$ bend %
Error:
- expected : U32
- observed : MNat
Context:
- n : MNat
- h : {dbl(n) == MZ{} : MNat}
- p : MNat
Location: use