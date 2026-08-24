# hypothesis/goal agreement through both scrutinee shapes: a variable
# match specializes hypothesis and goal together, and a computed match
# leaves both frozen at the call spelling -- in each twin the arm's h
# still meets the goal, so both proofs accept.
# ported from bend3: bend3 specialized computed hypotheses per arm;
# bend4 freezes computed matches whole, and the twins accept either way
type Nf:
  Zf{}
  Sf{p: Nf}

assert dbl:
  forall n: Nf
  Nf

def dbl(n):
  match n:
    case Zf{}:
      Zf{}
    case Sf{p}:
      Sf{Sf{dbl(p)}}

assert p_var:
  forall m: Nf
  forall h: {m == Zf{} : Nf}
  {m == Zf{} : Nf}

def p_var(m, h):
  match m:
    case Zf{}:
      h
    case Sf{p}:
      h

assert p_comp:
  forall n: Nf
  forall h: {dbl(n) == Zf{} : Nf}
  {dbl(n) == Zf{} : Nf}

def p_comp(n, h):
  match dbl(n):
    case Zf{}:
      h
    case Sf{p}:
      h

assert main:
  Nf

def main():
  Zf{}
$$ bend %
Zf{}
