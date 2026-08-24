# two fields of ONE constructor matched sequentially
# ported from bend3: a field binder cannot be re-matched inline (bend4's
# binder-order law), so the fields route through a helper def whose
# params match freely
type Nt:
  Z{}
  S{p: Nt}

type Duo:
  P{a: Nt, b: Nt}

assert go:
  forall x: Nt
  forall y: Nt
  Nt

def go(x, y):
  match x:
    case Z{}:
      y
    case S{p}:
      match y:
        case Z{}:
          p
        case S{q}:
          q

assert main:
  forall w: Duo
  Nt

def main(w):
  match w:
    case P{x, y}:
      go(x, y)
$$ bend % --show
go = \{Z: (y => y); S: (p => \{Z: p; S: (q => q)})}
main = \{P: (x => y => go(x, y))}
