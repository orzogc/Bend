# no funext: a λ never checks against an equation between functions
# (BendTT refuted the intro rule: rfl-only shed loses canonicity,
# value shed loses preservation). The pointwise proof is a Mismatch
# naming the offending term; proof_no_funext_000 pins the same with
# halting trusted.
# ported from bend3: local Nat renamed to N, the IH rewrite carries its
# explicit motive
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
37 | 
38>| def add_zero_eta(): x => add_zero(x)
39 |
