# def-form: a computed match on the def's own recursive call; the rows
# live in a helper def (bend4's idiom)
# ported from bend3: numerics become ctor words
type Nt:
  Zn{}
  Sn{p: Nt}

type W:
  Z{}
  S{p: W}

assert sel:
  forall r: W
  W

def sel(r):
  match r:
    case Z{}:
      S{Z{}}
    case k:
      Z{}

assert main:
  forall n: Nt
  W

def main(n):
  match n:
    case Zn{}:
      S{Z{}}
    case Sn{p}:
      sel(main(p))
$$ bend % --show
sel = \{Z: S{Z{}}; (r => Z{})}
main = \{Zn: S{Z{}}; Sn: (p => sel(main(p)))}

