# nested field match whose inner arms use the SIBLING field: t stays
# bound across the elimination of h
# ported from bend3: a field binder cannot be re-matched inline (bend4's
# binder-order law), so the fields route through a helper def
type Nt:
  Z{}
  S{p: Nt}

type Tree:
  Leaf{}
  Node{h: Nt, t: Nt}

assert go:
  forall h: Nt
  forall t: Nt
  Nt

def go(h, t):
  match h:
    case Z{}:
      t
    case S{p}:
      S{t}

assert main:
  forall w: Tree
  Nt

def main(w):
  match w:
    case Leaf{}:
      Z{}
    case Node{h, t}:
      go(h, t)
$$ bend % --show
go = \{Z: (t => t); S: (p => t => S{t})}
main = \{Leaf: Z{}; Node: (h => t => go(h, t))}
