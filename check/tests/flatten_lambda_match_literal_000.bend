# a \-match codomain family: the body IS the match-lambda, checked
# against the family applied to the bound argument
# ported from bend3: bend4's All binds a name (the family applies to it
# explicitly), literal results become ctors
type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

assert main:
  @b: Bl -> \{T: W; F: W}(b)

def main():
  \{T: S{Z{}}; F: Z{}}
$$ bend % --show
main = \{T: S{Z{}}; F: Z{}}
