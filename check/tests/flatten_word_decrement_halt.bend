# count-down loop shape: the miss branch's predecessor is structurally
# smaller (halt accepts)
# ported from bend3: 0/1+k become Z/S (bend4 has no number patterns)
type W:
  Z{}
  S{p: W}

assert main:
  forall k: W
  W

def main(k):
  match k:
    case Z{}:
      Z{}
    case S{k}:
      main(k)
$$ bend % --show
main = \{Z: Z{}; S: (k => main(k))}
