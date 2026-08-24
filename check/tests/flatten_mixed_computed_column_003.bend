# mixed group in argument order: a and b fuse as pattern columns, the
# computed id(b) feeds a helper's unused third param (bend4's match
# takes bare scrutinees; the kept b wears +)
# ported from bend3: literal arm values become ctors
import Base
type Nt:
  Zn{}
  Sn{p: Nt}

assert Nt.copy:
  forall t: Nt
  Copy(Nt, t) & Copy(Nt, t)

def Nt.copy(t):
  match t:
    case Zn{}:
      ((Zn{}, {==}), (Zn{}, {==}))
    case Sn{p}:
      ((px, pe), (py, pf)) = Nt.copy(p)
      s10 = Equal.cong(Nt, Nt, z => Sn{z}, p, px, pe)
      s20 = Equal.cong(Nt, Nt, z => Sn{z}, p, py, pf)
      ((Sn{px}, s10), (Sn{py}, s20))

type W:
  Z{}
  S{p: W}

assert id:
  forall n: Nt
  Nt

def id(n):
  n

assert sel:
  forall a: Nt
  forall b: Nt
  forall w: Nt
  W

def sel(a, b, w):
  match a, b:
    case Zn{}, Zn{}:
      Z{}
    case Zn{}, Sn{q}:
      S{Z{}}
    case Sn{p}, x:
      S{S{Z{}}}

assert main:
  forall a: Nt
  forall +b: +Nt
  W

def main(a, b):
  sel(a, b, id(b))
$$ bend % --show
Nt.copy = \{Zn: Tuple{Tuple{Zn{}, {==}}, Tuple{Zn{}, {==}}}; Sn: (p => \{Tuple: \{Tuple: (px => pe => \{Tuple: (py => pf => s10 = Equal.cong(Nt, Nt, z => Sn{z}, p, px, pe); s20 = Equal.cong(Nt, Nt, z => Sn{z}, p, py, pf); Tuple{Tuple{Sn{px}, s10}, Tuple{Sn{py}, s20}})})}}(Nt.copy(p)))}
id = n => n
sel = \{Zn: \{Zn: (w => Z{}); Sn: (q => w => S{Z{}})}; Sn: (p => b => w => S{S{Z{}}})}
main = a => b => sel(a, b, id(b))
