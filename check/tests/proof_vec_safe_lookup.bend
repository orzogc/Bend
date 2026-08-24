# FLAGSHIP: safe lookup on a length-indexed Vec -- the LT(i, n) bound
# discharges the empty case by the empty match and steps DEFINITIONALLY
# with the index (LT(S j, S p) = LT(j, p)); no default, total by the proof.
# ported from bend3: bend3's Base Nat.LT becomes a local LT(n, i) family
# (bend4 matches ride binder order, so the bound rides (n, i)); Nat
# payloads replace U32 so the answer prints literal
import Base

type N:
  Z{}
  S{p: N}

assert LT:
  forall n: N
  forall i: N
  Type

def LT(n, i):
  match n:
    case Z{}:
      Empty
    case S{p}:
      match i:
        case Z{}:
          Unit
        case S{j}:
          LT(p, j)

assert Vec:
  forall n: N
  Type

def Vec(n):
  match n:
    case Z{}:
      Unit
    case S{p}:
      (Nat & Vec(p))

assert vget:
  forall n: N
  forall xs: Vec(n)
  forall i: N
  forall e: LT(n, i)
  Nat

def vget(n, xs, i, e):
  match n:
    case Z{}:
      match e:
    case S{p}:
      (h, t) = xs
      match i:
        case Z{}:
          h
        case S{j}:
          vget(p, t, j, e)

assert main:
  Nat

def main(): vget(S{S{S{Z{}}}}, (10n, (20n, (30n, Unit{}))), S{S{Z{}}}, Unit{})

$$ bend %
30n
