# ragged nested matches: a default arm closes its level without touching
# the later columns (dominance), rigid rows below a default drive their
# own subgroups -- the flow shape, pinned structurally
# ported from bend3: numeric columns become ctor columns (W), literal
# arm values become ctors (bend4 has no number patterns)
type W:
  WZ{}
  WS{p: W}

type Nat:
  Z{}
  S{p: Nat}

type R:
  K100{}
  K200{}
  K300{}

assert main:
  forall d: W
  forall m: W
  forall n: Nat
  R

def main(d, m, n):
  match d:
    case WZ{}:
      K100{}
    case WS{d}:
      match m:
        case WZ{}:
          match n:
            case S{p}:
              main(d, WZ{}, p)
            case n:
              K200{}
        case m:
          K300{}
$$ bend % --show
main = \{WZ: (m => n => K100{}); WS: (d => \{WZ: \{S: (p => main(d, WZ{}, p)); (n => K200{})}; (m => n => K300{})})}
