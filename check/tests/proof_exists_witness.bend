# the full spec pipeline: forall evidence + exists sigma, filled by
# induction -- absurd arm via the empty match, witness built through a
# cong lemma, IH destructured from the recursive call; the witness
# computes.
# ported from bend3: bend3's `forall x where IsEven(x)` interleaved the
# evidence as its own parameter, which bend4 spells as a second forall
# clause; the explicit-motive cong closes the step
import Base

type N:
  Z{}
  S{p: N}

assert double:
  forall n: N
  N

def double(n):
  match n:
    case Z{}:
      Z{}
    case S{p}:
      S{S{double(p)}}

assert IsEven:
  forall n: N
  Type

def IsEven(n):
  match n:
    case Z{}:
      Unit
    case S{Z{}}:
      Empty
    case S{S{p}}:
      IsEven(p)

assert half_exists:
  forall x: N
  forall e: IsEven(x)
  exists y: N
  {double(y) == x : N}

assert cong_ss:
  forall -a: N
  forall -b: N
  forall e: {a == b : N}
  {S{S{a}} == S{S{b}} : N}

def cong_ss(a, b, e):
  %e : {S{S{a}} == S{S{_}} : N}
  {==}

def half_exists(x, e):
  match x:
    case Z{}:
      (Z{}, {==})
    case S{Z{}}:
      match e:
    case S{S{p}}:
      (y, pf) = half_exists(p, e)
      (S{y}, cong_ss(double(y), p, pf))

assert sample:
  &y: N -> {double(y) == S{S{S{S{Z{}}}}} : N}

def sample(): half_exists(S{S{S{S{Z{}}}}}, Unit{})

assert main:
  &y: N -> {double(y) == S{S{S{S{Z{}}}}} : N}

def main(): sample()

$$ bend %
Tuple{S{S{Z{}}}, {==}}
