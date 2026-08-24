# bend3's two-walks-plus-one-copy guard loses its counter (no --stats)
# and keeps its value: the tree is consumed by two whole walks, spelled
# with a +T5 Cop binder over the local T5.copy witness (bend3's
# over-use planted the copy), gen rides a Nat depth
import Base

type T5:
  Lf5{v: U32}
  Nd5{a: T5, b: T5}

assert T5.copy:
  forall t: T5
  Copy(T5, t) & Copy(T5, t)

def T5.copy(t):
  match t:
    case Lf5{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      s10 = Equal.cong(U32, T5, z => Lf5{z}, v, vx, ve)
      s20 = Equal.cong(U32, T5, z => Lf5{z}, v, vy, vf)
      ((Lf5{vx}, s10), (Lf5{vy}, s20))
    case Nd5{a, b}:
      ((ax, ae), (ay, af)) = T5.copy(a)
      ((bx, be), (by, bf)) = T5.copy(b)
      s10 = Equal.cong(T5, T5, z => Nd5{z, b}, a, ax, ae)
      s11 = Equal.cong(T5, T5, z => Nd5{ax, z}, b, bx, be)
      t11 = Equal.trans(T5, Nd5{a, b}, Nd5{ax, b}, Nd5{ax, bx}, s10, s11)
      s20 = Equal.cong(T5, T5, z => Nd5{z, b}, a, ay, af)
      s21 = Equal.cong(T5, T5, z => Nd5{ay, z}, b, by, bf)
      t21 = Equal.trans(T5, Nd5{a, b}, Nd5{ay, b}, Nd5{ay, by}, s20, s21)
      ((Nd5{ax, bx}, t11), (Nd5{ay, by}, t21))

assert gen:
  forall +d: +Nat
  forall +i: +U32
  T5

def gen(d, i):
  match d:
    case Zero{}:
      Lf5{i}
    case Succ{k}:
      Nd5{gen(k, i * 2), gen(k, i * 2 + 1)}

assert tsum:
  forall t: T5
  U32

def tsum(t):
  match t:
    case Lf5{v}:
      v
    case Nd5{a, b}:
      tsum(a) + tsum(b)

assert twice:
  forall +t: +T5
  U32

def twice(t):
  tsum(t) + tsum(t)

assert main.out:
  Nat

def main.out():
  U32.to_nat(twice(gen(4n, 1)))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
752n
$$ bend % --seq
752n
exit 0
$$ bend % --par
752n
exit 0
$$ bend % --js
752n
exit 0
