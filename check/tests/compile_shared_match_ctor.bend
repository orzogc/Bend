# over-used match, direct case tree: main over-uses x, so each call
# consumes its own copy; the catch-all binds the value whole
# ported from bend3: the share becomes a +let, the builder walks a Nat
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

assert val:
  forall x: Nt
  U32

def val(x):
  match x:
    case Zr{}:
      0
    case Sc{p}:
      U32.add(1, val(p))

assert pick:
  forall x: Nt
  U32

def pick(x):
  match x:
    case Zr{}:
      100
    case w:
      val(w)

assert nat:
  forall n: Nat
  Nt

def nat(n):
  match n:
    case 0n:
      Zr{}
    case 1n+m:
      Sc{nat(m)}

assert main.out:
  U32

def main.out():
  +x = {nat(5n) : +Nt}
  U32.add(pick(x), pick(x))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
10
$$ bend % --seq
10
exit 0
$$ bend % --par
10
exit 0
$$ bend % --js
10
exit 0
