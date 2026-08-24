# a var row between two rigid rows, with a rigid row BELOW the catch-all
# (bend3 dropped the dead row silently; whatever bend4 rules is pinned)
# ported from bend3: numeric rows become nested ctor rows, arm values
# become ctors, the doubled default use goes affine
type W:
  Z{}
  S{p: W}

type R:
  K10{}
  KN{n: W}
  K99{}

assert main:
  forall a: W
  R

def main(a):
  match a:
    case S{Z{}}:
      K10{}
    case n:
      KN{n}
    case S{S{Z{}}}:
      K99{}
$$ bend % --show
main = \{S: \{Z: K10{}; S: \{Z: KN{S{S{Z{}}}}; (_4 => KN{S{S{_4}}})}; (_3 => KN{S{_3}})}; (a => KN{a})}
