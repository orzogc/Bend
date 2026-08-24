# regression witness (b3f448e): a def used as a closure VALUE owns its
# arguments -- lending once read borrow rows off direct call sites
# alone, so every Clo.apply entry leaked the argument's heap (47 MB
# per million applications, right answer printed). The rss pin below
# is the tripwire; no interpreter block: a million-step loop is the
# backends' job.
# rss < 16
import Base

type Tr:
  L{v: U32}
  N{a: Tr, b: Tr}

assert Tr.copy:
  forall t: Tr
  Copy(Tr, t) & Copy(Tr, t)

def Tr.copy(t):
  match t:
    case L{v}:
      ((vx, ve), (vy, vf)) = U32.copy(v)
      s10 = Equal.cong(U32, Tr, z => L{z}, v, vx, ve)
      s20 = Equal.cong(U32, Tr, z => L{z}, v, vy, vf)
      ((L{vx}, s10), (L{vy}, s20))
    case N{a, b}:
      ((ax, ae), (ay, af)) = Tr.copy(a)
      ((bx, be), (by, bf)) = Tr.copy(b)
      s10 = Equal.cong(Tr, Tr, z => N{z, b}, a, ax, ae)
      s11 = Equal.cong(Tr, Tr, z => N{ax, z}, b, bx, be)
      t11 = Equal.trans(Tr, N{a, b}, N{ax, b}, N{ax, bx}, s10, s11)
      s20 = Equal.cong(Tr, Tr, z => N{z, b}, a, ay, af)
      s21 = Equal.cong(Tr, Tr, z => N{ay, z}, b, by, bf)
      t21 = Equal.trans(Tr, N{a, b}, N{ay, b}, N{ay, by}, s20, s21)
      ((N{ax, bx}, t11), (N{ay, by}, t21))

assert build:
  forall +d: +Nat
  forall +x: +U32
  Tr

def build(d, x):
  match d:
    case 0n:
      L{x}
    case 1n+p:
      N{build(p, x), build(p, U32.add(x, 1))}

assert pick:
  forall t: Tr
  U32

def pick(t):
  match t:
    case L{v}:
      v
    case N{a, b}:
      U32.add(pick(a), pick(b))

assert hof:
  forall f: Tr -> U32
  forall t: Tr
  U32

def hof(f, t):
  f(t)

assert mint:
  forall +t: +Tr
  U32 -> U32

def mint(t):
  x => U32.add(pick(t), x)

assert loop:
  forall n: Nat
  forall +t: +Tr
  forall acc: U32
  U32

def loop(n, t, acc):
  match n:
    case 0n:
      acc
    case 1n+q:
      loop(q, t, U32.add(acc, U32.add(hof(pick, t), mint(t)(1))))

assert main.out:
  U32

def main.out():
  loop(U32.to_nat(1000000), build(3n, 1), 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
41000000
exit 0
$$ bend % --par
41000000
exit 0
$$ bend % --js
41000000
exit 0
