# a DEPENDENT family: the match codomain mentions an earlier binder n;
# each arm's goal reduces per constructor
# ported from bend3: bend4's All binds a name, so the family applies to
# it explicitly and the body is the match-lambda itself
type Nt:
  Z{}
  S{p: Nt}

type Bl:
  T{}
  F{}

assert main:
  @n: Nt -> @b: Bl -> \{T: {n == n : Nt}; F: Nt}(b)

def main():
  n => \{T: {==}; F: n}
$$ bend % --show
main = n => \{T: {==}; F: n}
