# no funext: a λ never checks against an equation between functions
# (BendTT refuted the intro rule).
# ported from bend3: bend3 pinned this under --no-halt; bend4 needs no
# pragma at all -- every def here descends structurally, and the
# refusal is the checker's own, strict
type N:
  Z{}
  S{p: N}

assert add:
  forall n: N
  forall m: N
  N

def add(n, m):
  match n:
    case Z{}:
      m
    case S{k}:
      S{add(k, m)}

assert add_zero:
  forall n: N
  {add(n, Z{}) == n : N}

def add_zero(n):
  match n:
    case Z{}:
      {==}
    case S{k}:
      %add_zero(k) : {S{add(k, Z{})} == S{_} : N}; {==}

assert add_zero_eta:
  {(x => add(x, Z{})) == (x => x) : N -> N}

def add_zero_eta(): x => add_zero(x)

assert main:
  N

def main(): Z{}

$$ bend %
Error:
- expected : {(x => add(x, Z{})) == (x => x) : @_:N -> N}
- observed : x => add_zero(x)
Location: add_zero_eta
35 | 
36>| def add_zero_eta(): x => add_zero(x)
37 |
