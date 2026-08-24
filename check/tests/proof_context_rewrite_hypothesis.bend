# Context rewriting: prove {x==b} from {x==a} and {a==b} by rewriting the HYPOTHESIS.
# ported from bend3: bend4's rewrite is goal-only J with an explicit motive, and
# the goal motive {x == _} already closes this -- the hypothesis y proves the
# rewritten goal directly, no per-hypothesis context rewrite exists or is needed
type N:
  Z{}
  S{p: N}

assert trans:
  @-x: N -> @-a: N -> @-b: N -> {a == b : N} -> {x == a : N} -> {x == b : N}

def trans(): x => a => b => e => y => %e : {x == _ : N}; y

assert main:
  N

def main(): Z{}

$$ bend %
Z{}
