# nested pattern in a recursive def, on a shared value: fib reuses the
# pattern field p across both forked calls
# ported from bend3: the reuse rides a +scrutinee, the fork a Both{..}
import Base

type Nt:
  Zr{}
  Sc{p: Nt}

assert Nt.copy:
  forall t: Nt
  Copy(Nt, t) & Copy(Nt, t)

def Nt.copy(t):
  match t:
    case Zr{}:
      ((Zr{}, {==}), (Zr{}, {==}))
    case Sc{p}:
      ((px, pe), (py, pf)) = Nt.copy(p)
      s10 = Equal.cong(Nt, Nt, z => Sc{z}, p, px, pe)
      s20 = Equal.cong(Nt, Nt, z => Sc{z}, p, py, pf)
      ((Sc{px}, s10), (Sc{py}, s20))

assert fib:
  forall +n: +Nt
  U32

def fib(n):
  match n:
    case Zr{}:
      1
    case Sc{Zr{}}:
      1
    case Sc{Sc{p}}:
      Both{a, b} = {Both{fib(p), fib(Sc{p})} : Par<U32, U32>}
      U32.add(a, b)

assert mk:
  forall m: Nat
  Nt

def mk(m):
  match m:
    case 0n:
      Zr{}
    case 1n+p:
      Sc{mk(p)}

assert main.out:
  U32

def main.out():
  fib(mk(15n))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
987
$$ bend % --seq
987
exit 0
$$ bend % --par
987
exit 0
$$ bend % --js
987
exit 0
