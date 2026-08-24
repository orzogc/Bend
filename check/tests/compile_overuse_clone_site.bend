# over-use pays clones: keep retains x's nodes in its result, so each
# extra use pays a copy and the last use owns
# ported from bend3: the counter walks a Nat, the share a +param
import Base

type Tr:
  Lf{v: U32}
  Nd{a: Tr, b: Tr}

assert Tr.copy:
  forall t: Tr
  Copy(Tr, t) & Copy(Tr, t)

def Tr.copy(t):
  match t:
    case Lf{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      s10 = Equal.cong(U32, Tr, z => Lf{z}, v, vx, ve)
      s20 = Equal.cong(U32, Tr, z => Lf{z}, v, vy, vf)
      ((Lf{vx}, s10), (Lf{vy}, s20))
    case Nd{a, b}:
      ((ax, ae), (ay, af)) = Tr.copy(a)
      ((bx, be), (by, bf)) = Tr.copy(b)
      s10 = Equal.cong(Tr, Tr, z => Nd{z, b}, a, ax, ae)
      s11 = Equal.cong(Tr, Tr, z => Nd{ax, z}, b, bx, be)
      t11 = Equal.trans(Tr, Nd{a, b}, Nd{ax, b}, Nd{ax, bx}, s10, s11)
      s20 = Equal.cong(Tr, Tr, z => Nd{z, b}, a, ay, af)
      s21 = Equal.cong(Tr, Tr, z => Nd{ay, z}, b, by, bf)
      t21 = Equal.trans(Tr, Nd{a, b}, Nd{ay, b}, Nd{ay, by}, s20, s21)
      ((Nd{ax, bx}, t11), (Nd{ay, by}, t21))

assert gen:
  forall +d: +Nat
  forall +i: +U32
  Tr

def gen(d, i):
  match d:
    case 0n:
      Lf{i}
    case 1n+p:
      Nd{gen(p, U32.mul(i, 2)), gen(p, U32.add(U32.mul(i, 2), 1))}

assert keep:
  forall x: Tr
  Tr

def keep(x):
  match x:
    case Lf{v}:
      Lf{v}
    case Nd{a, b}:
      Nd{a, b}

assert tsum:
  forall t: Tr
  U32

def tsum(t):
  match t:
    case Lf{v}:
      v
    case Nd{a, b}:
      U32.add(tsum(a), tsum(b))

assert foo:
  forall +x: +Tr
  U32

def foo(x):
  a = keep(x)
  b = keep(x)
  U32.add(tsum(a), tsum(b))

assert main.out:
  U32

def main.out():
  foo(gen(5n, 1))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
3040
$$ bend % --seq
3040
exit 0
$$ bend % --par
3040
exit 0
$$ bend % --js
3040
exit 0
