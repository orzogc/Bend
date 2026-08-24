# regression witness (10225ce): the compiler is a pure function of its
# input -- the borrow table once outlived compile_book, so the SECOND
# compilation in one process read the first book's stale lent rows,
# term_uses skipped the lent capture, and the minted continuation died
# 'unbound binder: t' on THIS exact shape (lend's row survives the
# borrow fixpoint: its site is held by eat's, sum's arg rides lend's
# root, and spin's cut mints a continuation whose only use of t is the
# lent sum call). The runner's reg_compiler_pure row recompiles this
# file in-process and byte-compares the emissions.
import Base

type Bt:
  Bl{v: U32}
  Bn{a: Bt, b: Bt}

assert Bt.copy:
  forall t: Bt
  Copy(Bt, t) & Copy(Bt, t)

def Bt.copy(t):
  match t:
    case Bl{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      s10 = Equal.cong(U32, Bt, z => Bl{z}, v, vx, ve)
      s20 = Equal.cong(U32, Bt, z => Bl{z}, v, vy, vf)
      ((Bl{vx}, s10), (Bl{vy}, s20))
    case Bn{a, b}:
      ((ax, ae), (ay, af)) = Bt.copy(a)
      ((bx, be), (by, bf)) = Bt.copy(b)
      s10 = Equal.cong(Bt, Bt, z => Bn{z, b}, a, ax, ae)
      s11 = Equal.cong(Bt, Bt, z => Bn{ax, z}, b, bx, be)
      t11 = Equal.trans(Bt, Bn{a, b}, Bn{ax, b}, Bn{ax, bx}, s10, s11)
      s20 = Equal.cong(Bt, Bt, z => Bn{z, b}, a, ay, af)
      s21 = Equal.cong(Bt, Bt, z => Bn{ay, z}, b, by, bf)
      t21 = Equal.trans(Bt, Bn{a, b}, Bn{ay, b}, Bn{ay, by}, s20, s21)
      ((Bn{ax, bx}, t11), (Bn{ay, by}, t21))

assert sum:
  forall t: Bt
  U32

def sum(t):
  match t:
    case Bl{v}:
      v
    case Bn{a, b}:
      U32.add(sum(a), sum(b))

assert spin:
  forall +n: +Nat
  U32

def spin(n):
  match n:
    case 0n:
      1
    case 1n+p:
      U32.add(1, spin(p))

assert lend:
  forall t: Bt
  U32

def lend(t):
  a = spin(3n)
  U32.add(a, sum(t))

assert eat:
  forall t: Bt
  U32

def eat(t):
  match t:
    case Bl{v}:
      v
    case Bn{a, b}:
      U32.add(eat(a), eat(b))

assert main.out:
  U32

def main.out():
  +t = {Bn{Bn{Bl{1}, Bl{2}}, Bl{3}} : +Bt}
  a = lend(t)
  U32.add(a, eat(t))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
16
$$ bend % --seq
16
exit 0
$$ bend % --par
16
exit 0
$$ bend % --js
16
exit 0
