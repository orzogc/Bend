# bend3 pinned `x = v; match x` (a let-var match is a computed match);
# bend4 agrees: the let variable's match flattens to the match-lambda
# applied to the variable under the let
type Nt:
  Z{}
  S{p: Nt}

assert main:
  forall v: Nt
  Nt

def main(v):
  x = v
  match x:
    case Z{}:
      Z{}
    case S{p}:
      p
$$ bend % --show
main = v => x = v; \{Z: Z{}; S: (p => p)}(x)
