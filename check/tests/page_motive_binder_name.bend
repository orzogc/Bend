# a rewrite under dependent hypotheses about the same equation checks
# clean -- no ill-typed-rebind page exists (bend4's rewrite is
# goal-only J, so h2/h3 are never rebound)
import Base
type N:
  NZ{}
  NS{p: N}

assert add:
  forall a: N
  forall b: N
  N

def add(a, b):
  match a:
    case NZ{}:
      b
    case NS{p}:
      NS{add(p, b)}

assert f:
  forall n: N
  forall e: {add(n, NZ{}) == NZ{} : N}
  forall h2: {add(n, NZ{}) == NZ{} : N}
  forall h3: {h2 == h2 : {add(n, NZ{}) == NZ{} : N}}
  N

def f(n, e, h2, h3):
  %e : N
  NZ{}

$$ bend %
