# deep nesting traffic: a 4-deep right-nested tuple fully opened and
# rebuilt reversed; a record-of-records rebuilt with one deep field bumped
# ported from bend3: tuple destructures ride helper defs (a bend4
# pattern-let wants a binder-consuming call on the right)
import Base

type Inner:
  I2{x: U32, y: U32}

type Outer:
  O3{a: Inner, b: Inner, n: U32}

assert bump.at:
  forall b: Inner
  forall a: Inner
  forall n: U32
  Outer

def bump.at(b, a, n):
  match b:
    case I2{bx, by}:
      O3{a, I2{bx, U32.add(by, 10)}, n}

assert bump:
  forall o: Outer
  Outer

def bump(o):
  match o:
    case O3{a, b, n}:
      bump.at(b, a, n)

assert odig.b:
  forall b: Inner
  forall ax: U32
  forall ay: U32
  forall n: U32
  U32

def odig.b(b, ax, ay, n):
  match b:
    case I2{bx, by}:
      U32.add(U32.add(U32.add(U32.add(ax, U32.mul(ay, 10)), U32.mul(bx, 100)), U32.mul(by, 1000)), U32.mul(n, 10000))

assert odig.a:
  forall a: Inner
  forall b: Inner
  forall n: U32
  U32

def odig.a(a, b, n):
  match a:
    case I2{ax, ay}:
      odig.b(b, ax, ay, n)

assert odig:
  forall o: Outer
  U32

def odig(o):
  match o:
    case O3{a, b, n}:
      odig.a(a, b, n)

assert flip:
  forall t: (U32 & U32 & U32 & U32 & U32)
  (U32 & U32 & U32 & U32 & U32)

def flip(t):
  (a, b, c, d, e) = t
  (e, d, c, b, a)

assert tdig:
  forall t: (U32 & U32 & U32 & U32 & U32)
  U32

def tdig(t):
  (p, q, r, s, u) = t
  U32.add(U32.add(U32.add(U32.add(U32.mul(p, 10000), U32.mul(q, 1000)), U32.mul(r, 100)), U32.mul(s, 10)), u)

assert main.out:
  U32

def main.out():
  tup = tdig(flip((1, (2, (3, (4, 5))))))
  rec = odig(bump(O3{I2{1, 2}, I2{3, 4}, 9}))
  U32.add(tup, rec)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
158642
$$ bend % --seq
158642
exit 0
$$ bend % --par
158642
exit 0
$$ bend % --js
158642
exit 0
