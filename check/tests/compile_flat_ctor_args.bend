# flat-class ctor args: a recursive def taking a nested record, call
# sites passing inline ctor literals and a call-valued subfield
# ported from bend3: counters walk Nats; strict -- the record's inner
# counter cannot carry structural descent through the rebuilt ctor, so
# the loop rides a leading Nat fuel column, reused words +U32
import Base

type Inn:
  Ii{x: U32, y: U32}

type Outt:
  Oo{i: Inn, z: Nat}

assert lenof:
  forall i: Inn
  U32

def lenof(i):
  match i:
    case Ii{x, y}:
      U32.add(x, y)

assert mkin:
  forall n: Nat
  Inn

def mkin(n):
  match n:
    case 0n:
      Ii{1, 2}
    case 1n+p0:
      +p = {p0 : +Nat}
      Ii{U32.add(1, U32.from_nat(p)), lenof(mkin(p))}

assert use:
  forall fuel: Nat
  forall o: Outt
  forall acc: U32
  U32

def use(fuel, o, acc):
  match fuel o:
    case 0n _:
      acc
    case 1n+f Oo{Ii{x, y}, 0n}:
      U32.add(U32.add(acc, x), y)
    case 1n+f Oo{Ii{x0, y}, 1n+z2}:
      +x = {x0 : +U32}
      use(f, Oo{Ii{U32.add(x, 1), y}, z2}, U32.add(acc, x))

assert main.out:
  U32

def main.out():
  use(3n, Oo{mkin(3n), 2n}, 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
18
$$ bend % --seq
18
exit 0
$$ bend % --par
18
exit 0
$$ bend % --js
18
exit 0
