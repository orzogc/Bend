# recursion through nested checker-minted split auxes: a value matched
# via a computed group, the inner group rebinding it through a typed
# local, the pattern Sc{Sc{p}} feeding the recursive call
# ported from bend3: the shared scrutinee becomes a +param (a local
# Nt.copy witness licenses it), and the recursion rides a Nat fuel
# matched ahead of the group (the queens shape): the aux chain hides
# the shrinking column, the fuel is the one the descent sees
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

type Bl:
  Tt{}
  Ff{}

assert Nt.copy:
  forall t: Nt
  Copy(Nt, t) & Copy(Nt, t)

def Nt.copy(t):
  match t:
    case Zr{}:
      ((Zr{}, {==}), (Zr{}, {==}))
    case Sc{p}:
      ((px, pe), (py, pf)) = Nt.copy(p)
      s1 = Equal.cong(Nt, Nt, z => Sc{z}, p, px, pe)
      s2 = Equal.cong(Nt, Nt, z => Sc{z}, p, py, pf)
      ((Sc{px}, s1), (Sc{py}, s2))

assert big:
  forall a: Nt
  Bl

def big(a):
  match a:
    case Zr{}:
      Ff{}
    case Sc{Zr{}}:
      Ff{}
    case Sc{Sc{p}}:
      Tt{}

assert cnt:
  forall f: Nat
  forall +n: +Nt
  U32

def cnt(f, n):
  match f:
    case 0n:
      0
    case 1n+g:
      match big(n):
        case Tt{}:
          match m : Nt = n:
            case Sc{Sc{p}}:
              U32.add(2, cnt(g, p))
            case Sc{Zr{}}:
              1
            case Zr{}:
              1
            return U32
        case Ff{}:
          0

assert main.out:
  U32

def main.out():
  n = {Sc{Sc{Sc{Zr{}}}} : Nt}
  cnt(4n, n)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2
$$ bend % --seq
2
exit 0
$$ bend % --par
2
exit 0
$$ bend % --js
2
exit 0
