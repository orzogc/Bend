# Context rewriting also transports a VALUE hypothesis across a type-family equality.
# ported from bend3: in bend4 the transport is the goal-only J rewrite at the
# type-family motive fam(_) -- the goal fam(b) rewrites to fam(a), which y proves
type Uni:
  U{}
type Emp:
type N:
  Z{}
  S{p: N}

assert fam:
  forall n: N
  Type

def fam(n):
  match n:
    case Z{}:
      Uni
    case S{k}:
      Emp

assert castF:
  @-a: N -> @-b: N -> {a == b : N} -> fam(a) -> fam(b)

def castF(): a => b => e => y => %e : fam(_); y

assert main:
  fam(Z{})

def main(): castF(Z{}, Z{}, {==}, U{})

$$ bend %
U{}
