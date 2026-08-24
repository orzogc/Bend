# loop-record unpack, wide and copied: an 8-field record rides the back
# edge, and a copy of an over-used record enters the loop (pick's
# catch-all binds it whole)
# ported from bend3: counters walk Nats, the share becomes a +let
import Base

type Oct:
  MkOct{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

assert whirl:
  forall +i: +Nat
  forall st: Oct
  U32

def whirl(i, st):
  match i:
    case 0n:
      MkOct{a, b, c, d, e, f, g, h} = st
      U32.mod(U32.add(U32.add(U32.add(a, b), U32.add(c, d)), U32.add(U32.add(e, f), U32.add(g, h))), 65521)
    case 1n+p:
      MkOct{a, b, c, d, e, f, g, h} = st
      whirl(p, MkOct{b, c, d, e, f, g, h, U32.mod(U32.add(a, U32.add(1, U32.from_nat(p))), 65521)})

type St:
  MkSt{a: U32, b: U32}

assert St.copy:
  forall t: St
  Copy(St, t) & Copy(St, t)

def St.copy(t):
  match t:
    case MkSt{a, b}:
      ((ax, ae), (ay, af)) = U32.copy(a)
      ((bx, be), (by, bf)) = U32.copy(b)
      s10 = Equal.cong(U32, St, z => MkSt{z, b}, a, ax, ae)
      s11 = Equal.cong(U32, St, z => MkSt{ax, z}, b, bx, be)
      t11 = Equal.trans(St, MkSt{a, b}, MkSt{ax, b}, MkSt{ax, bx}, s10, s11)
      s20 = Equal.cong(U32, St, z => MkSt{z, b}, a, ay, af)
      s21 = Equal.cong(U32, St, z => MkSt{ay, z}, b, by, bf)
      t21 = Equal.trans(St, MkSt{a, b}, MkSt{ay, b}, MkSt{ay, by}, s20, s21)
      ((MkSt{ax, bx}, t11), (MkSt{ay, by}, t21))

assert read:
  forall x: St
  U32

def read(x):
  match x:
    case MkSt{a, b}:
      U32.add(a, b)

assert own_go:
  forall +i: +Nat
  forall st: St
  U32

def own_go(i, st):
  match i:
    case 0n:
      MkSt{a, b} = st
      U32.add(a, b)
    case 1n+p:
      MkSt{a, b} = st
      own_go(p, MkSt{b, U32.add(a, U32.add(1, U32.from_nat(p)))})

assert pick:
  forall x: St
  U32

def pick(x):
  match x:
    case w:
      own_go(6n, w)

assert main.out:
  U32

def main.out():
  +s = {MkSt{10, 20} : +St}
  U32.add(U32.add(whirl(11n, MkOct{1, 2, 3, 4, 5, 6, 7, 8}), read(s)), pick(s))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
183
$$ bend % --seq
183
exit 0
$$ bend % --par
183
exit 0
$$ bend % --js
183
exit 0
