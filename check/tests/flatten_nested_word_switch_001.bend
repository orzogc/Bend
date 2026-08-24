# nested word switches, param x param: ctor arms and defaults at both
# levels
# ported from bend3: numeric columns become ctor columns, literal arm
# values become ctors (bend4 has no number patterns)
type W:
  Z{}
  S{p: W}

type R:
  K1{}
  K2{}
  K3{}
  K4{}

assert main:
  forall a: W
  forall b: W
  R

def main(a, b):
  match a:
    case Z{}:
      match b:
        case Z{}:
          K1{}
        case m:
          K2{}
    case n:
      match b:
        case Z{}:
          K3{}
        case m:
          K4{}
$$ bend % --show
main = \{Z: \{Z: K1{}; (b => K2{})}; (a => \{Z: K3{}; (b => K4{})})}
