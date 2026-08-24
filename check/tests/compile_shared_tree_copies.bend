# a tree used twice: the extra use pays a copy; peek opens two levels
# deep while sum walks whole, both off one binder
# ported from bend3: counters walk Nats, forks become Both{..} pairs,
# the share a +param
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
      Both{l, r} = {Both{gen(p, U32.mul(i, 2)), gen(p, U32.add(U32.mul(i, 2), 1))} : Par<Tr, Tr>}
      Nd{l, r}

assert sum:
  forall t: Tr
  U32

def sum(t):
  match t:
    case Lf{v}:
      v
    case Nd{a, b}:
      Both{x, y} = {Both{sum(a), sum(b)} : Par<U32, U32>}
      U32.add(x, y)

assert peek:
  forall t: Tr
  U32

def peek(t):
  match t:
    case Lf{v}:
      v
    case Nd{Lf{v}, b}:
      s = sum(b)
      U32.add(v, s)
    case Nd{Nd{aa, ab}, b}:
      Both{x, y} = {Both{sum(aa), sum(ab)} : Par<U32, U32>}
      z = sum(b)
      U32.add(x, U32.add(y, z))

assert dup_use:
  forall +t: +Tr
  U32

def dup_use(t):
  Both{a, b} = {Both{sum(t), peek(t)} : Par<U32, U32>}
  U32.add(a, b)

assert main.out:
  U32

def main.out():
  dup_use(gen(4n, 1))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
752
$$ bend % --seq
752
exit 0
$$ bend % --par
752
exit 0
$$ bend % --js
752
exit 0
