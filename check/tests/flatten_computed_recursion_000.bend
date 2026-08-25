# recursion through a computed match: the decision factors into a
# helper def (bend4's idiom: a match heads a def body; a computed
# match is the applied match-lambda), and the kept scrutinee wears +
# (a local Nt.copy witness licenses it)
# ported from bend3: literal arm values become ctors; bend3's mutual
# deep<->main pair folds into ONE def -- the deep step spelled as a
# nested match-lambda arm -- whose recursion rides a Nat fuel matched
# ahead of the computed match (the queens shape)
import Base

type Nt:
  Zn{}
  Sn{p: Nt}

type Bl:
  T{}
  F{}

type W:
  Z{}
  S{p: W}

assert Nt.copy:
  forall t: Nt
  Copy(Nt, t) & Copy(Nt, t)

def Nt.copy(t):
  match t:
    case Zn{}:
      ((Zn{}, {==}), (Zn{}, {==}))
    case Sn{p}:
      ((px, pe), (py, pf)) = Nt.copy(p)
      s1 = Equal.cong(Nt, Nt, z => Sn{z}, p, px, pe)
      s2 = Equal.cong(Nt, Nt, z => Sn{z}, p, py, pf)
      ((Sn{px}, s1), (Sn{py}, s2))

assert big:
  forall a: Nt
  Bl

def big(a):
  match a:
    case Zn{}:
      F{}
    case Sn{Zn{}}:
      F{}
    case Sn{Sn{p}}:
      T{}

assert main:
  forall f: Nat
  forall +n: +Nt
  W

def main(f, n):
  match f:
    case 0n:
      Z{}
    case 1n+g:
      \{T: \{Sn: \{Sn: (p => S{S{main(g, p)}}); Zn: S{Z{}}}; Zn: S{Z{}}}(n); F: Z{}}(big(n))
$$ bend % --show
Nt.copy = \{Zn: Tuple{Tuple{Zn{}, {==}}, Tuple{Zn{}, {==}}}; Sn: (p => \{Tuple: \{Tuple: (px => pe => \{Tuple: (py => pf => s1 = Equal.cong(Nt, Nt, z => Sn{z}, p, px, pe); s2 = Equal.cong(Nt, Nt, z => Sn{z}, p, py, pf); Tuple{Tuple{Sn{px}, s1}, Tuple{Sn{py}, s2}})})}}(Nt.copy(p)))}
big = \{Zn: F{}; Sn: \{Zn: F{}; Sn: (p => T{})}}
main = \{Zero: (n => Z{}); Succ: (g => n => \{T: \{Sn: \{Sn: (p => S{S{main(g, p)}}); Zn: S{Z{}}}; Zn: S{Z{}}}(n); F: Z{}}(big(n)))}
