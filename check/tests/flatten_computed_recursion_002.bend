# a SELF scrutinee: a computed match on the def's own recursive call;
# the literal-plus-default rows live in a helper def (bend4's idiom)
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
    case S{Z{}}:
      Z{}
    case k:
      S{Z{}}

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
sel = \{S: \{Z: Z{}; (_3 => S{Z{}})}; (r => S{Z{}})}
main = \{Zn: S{Z{}}; Sn: (p => sel(main(p)))}

