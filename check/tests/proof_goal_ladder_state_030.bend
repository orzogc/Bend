# goal ladder, Ford elimination ESS-arm: goal Emp, eq refined to
# {S{Z{}} == S{S{p}}}.
# ported from bend3: the ladder rides the ported bend4 development, so
# the pinned page is bend4's own goal at the same proof state
type Uni:
  U{}
type Emp:

type N:
  Z{}
  S{p: N}

type Even<-n: N>:
  EZ{eq: {n == Z{} : N}}
  ESS{p: N, e: Even<p>, eq: {n == S{S{p}} : N}}

assert NatD:
  forall x: N
  forall zc: Type
  forall sc: Type
  Type

def NatD(x, zc, sc):
  match x:
    case Z{}:
      zc
    case S{q}:
      sc

assert refute_ez:
  forall eq: {S{Z{}} == Z{} : N}
  Emp

def refute_ez(eq):
  %eq : NatD(_, Emp, Uni)
  U{}

assert one_odd:
  forall ev: Even<S{Z{}}>
  Emp

def one_odd(ev):
  match ev:
    case EZ{eq}:
      refute_ez(eq)
    case ESS{p, e, eq}:
      Type

$$ bend %
Error:
- expected : Emp
- observed : Type
Context:
- p  : N
- e  : Even<p>
- eq : {S{Z{}} == S{S{p}} : N}
Location: one_odd
46 |     case ESS{p, e, eq}:
47>|       Type
48 |
