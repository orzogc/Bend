# a pattern column beside a value column: every row binds the value as
# a var, riding it through the match
# ported from bend3: the computed x+1 becomes the ctor build S{x} bound
# through the var column (bend4's match takes bare scrutinees)
type Nt:
  Zn{}
  Sn{p: Nt}

type W:
  Z{}
  S{p: W}

assert main:
  forall n: Nt
  forall x: W
  W

def main(n, x):
  match n, x:
    case Zn{}, x:
      S{x}
    case Sn{p}, x:
      main(p, S{x})
$$ bend % --show
main = \{Zn: (x => S{x}); Sn: (p => x => main(p, S{x}))}
