#[halts]
# recursion through nested checker-minted split auxes: a value matched
# via a computed group, the inner group rebinding it through a typed
# local, the pattern Sc{Sc{p}} feeding the recursive call
# ported from bend3: the shared scrutinee becomes a +param
# strict is impossible for this subject, probed: a computed scrutinee
# takes an internal binder, so under the group every earlier binder is
# out of order for an inner structural match -- the typed local, a
# pre-bound annotated +rebind and the +param itself all refuse the
# same way, and only inverting the subject (structural match outside,
# the group inside the arms) checks, so the pragma carries the shape
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

type Bl:
  Tt{}
  Ff{}

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
  forall +n: Nt
  U32

def cnt(n):
  match big(n):
    case Tt{}:
      match m : Nt = n:
        case Sc{Sc{p}}:
          U32.add(2, cnt(p))
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
  cnt(n)

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
