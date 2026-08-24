# the Ford trick (parameters + equation fields recover GADTs): Even(n)
# evidence is built with {==} fields, and eliminated by matching -- each
# arm's eq field specializes, refuted via motive transport + succ_inj.
# ported from bend3: transport motives flip to bend4's right-into-left
# fold; the lambda motives become _-bound motive terms
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
    case S{p}:
      sc

assert z_ne_s:
  forall -p: N
  forall e: {Z{} == S{p} : N}
  Emp

def z_ne_s(p, e):
  %e : NatD(_, Uni, Emp)
  U{}

assert s_ne_z:
  forall -p: N
  forall e: {S{p} == Z{} : N}
  Emp

def s_ne_z(p, e):
  %e : NatD(_, Emp, Uni)
  U{}

assert pred:
  forall n: N
  N

def pred(n):
  match n:
    case Z{}:
      Z{}
    case S{p}:
      p

assert s_inj:
  forall -a: N
  forall -b: N
  forall e: {S{a} == S{b} : N}
  {a == b : N}

def s_inj(a, b, e):
  %e : {a == pred(_) : N}
  {==}

assert two_even:
  Even<S{S{Z{}}}>

def two_even(): ESS{Z{}, EZ{{==}}, {==}}

assert one_odd:
  forall ev: Even<S{Z{}}>
  Emp

def one_odd(ev):
  match ev:
    case EZ{eq}:
      s_ne_z(Z{}, eq)
    case ESS{p, e, eq}:
      z_ne_s(p, s_inj(Z{}, S{p}, eq))

$$ bend %
