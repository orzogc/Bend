# bend3's pair wall, both halves carried: a pair of Data components
# contracted freely while a closure-holding pair refused multi-use.
# bend4 is affine for every type: the free half is twice's +p Cop
# binder over Pair.copy, and the wall half refuses at leak the same
# way --
# leak's bare p spends twice, closure or not.
# ported from bend3: leak's let-then-destructure routes through
# leak.go; unused destructure components simply drop
import Base

assert Pair.copy:
  forall -c1: Copiable(U32)
  forall -c2: Copiable(U32)
  forall t: U32 & U32
  Copy(U32 & U32, t) & Copy(U32 & U32, t)

def Pair.copy(c1, c2, t):
  (a, b) = t
  ((ax, ae), (ay, af)) = U32.copy(a)
  ((bx, be), (by, bf)) = U32.copy(b)
  s10 = Equal.cong(U32, U32 & U32, z => (z, b), a, ax, ae)
  s11 = Equal.cong(U32, U32 & U32, z => (ax, z), b, bx, be)
  t11 = Equal.trans(U32 & U32, (a, b), (ax, b), (ax, bx), s10, s11)
  s20 = Equal.cong(U32, U32 & U32, z => (z, b), a, ay, af)
  s21 = Equal.cong(U32, U32 & U32, z => (ay, z), b, by, bf)
  t21 = Equal.trans(U32 & U32, (a, b), (ay, b), (ay, by), s20, s21)
  (((ax, bx), t11), ((ay, by), t21))

assert pa:
  forall p: U32 & U32
  U32

def pa(p):
  (a, b) = p
  a

assert pb:
  forall p: U32 & U32
  U32

def pb(p):
  (a, b) = p
  b

assert twice:
  forall +p: (+ (U32 & U32) ~ Pair.copy(U32.copy, U32.copy))
  U32

def twice(p):
  pa(p) + pb(p)

assert la:
  forall p: U32 & (U32 -> U32)
  U32

def la(p):
  (a, f) = p
  a

assert leak.go:
  forall p: U32 & (U32 -> U32)
  forall x: U32
  U32

def leak.go(p, x):
  (a, f) = p
  f(x)

assert leak:
  forall p: U32 & (U32 -> U32)
  U32

def leak(p):
  leak.go(p, la(p))

assert main:
  U32

def main(): twice((2, 3))
$$ bend %
Error:
- expected : p
- observed : p (consumed more than once)
Location: leak
