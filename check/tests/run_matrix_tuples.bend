# tuples as data: 2x2 matrices of words as nested pairs, multiplied and
# squared; ((1,1),(1,0))^4 carries fib in its cells
# ported from bend3: cell reuse rides annotated + rebinding (Cop);
# destructures happen in helper defs; strict -- the squared matrix
# rides a nested-pair Copy witness built on Pair.copy
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

assert Mat.copy:
  forall -c: Copiable(U32 & U32)
  forall t: (U32 & U32) & (U32 & U32)
  Copy((U32 & U32) & (U32 & U32), t) & Copy((U32 & U32) & (U32 & U32), t)

def Mat.copy(c, t):
  (p, q) = t
  ((px, pe), (py, pf)) = Pair.copy(U32.copy, U32.copy, p)
  ((qx, qe), (qy, qf)) = Pair.copy(U32.copy, U32.copy, q)
  s10 = Equal.cong(U32 & U32, (U32 & U32) & (U32 & U32), z => (z, q), p, px, pe)
  s11 = Equal.cong(U32 & U32, (U32 & U32) & (U32 & U32), z => (px, z), q, qx, qe)
  t11 = Equal.trans((U32 & U32) & (U32 & U32), (p, q), (px, q), (px, qx), s10, s11)
  s20 = Equal.cong(U32 & U32, (U32 & U32) & (U32 & U32), z => (z, q), p, py, pf)
  s21 = Equal.cong(U32 & U32, (U32 & U32) & (U32 & U32), z => (py, z), q, qy, qf)
  t21 = Equal.trans((U32 & U32) & (U32 & U32), (p, q), (py, q), (py, qy), s20, s21)
  (((px, qx), t11), ((py, qy), t21))

assert mmul:
  forall m: ((U32 & U32) & (U32 & U32))
  forall n: ((U32 & U32) & (U32 & U32))
  ((U32 & U32) & (U32 & U32))

def mmul(m, n):
  ((a0, b0), (c0, d0)) = m
  ((e0, f0), (g0, h0)) = n
  +a = {a0 : +U32}
  +b = {b0 : +U32}
  +c = {c0 : +U32}
  +d = {d0 : +U32}
  +e = {e0 : +U32}
  +f = {f0 : +U32}
  +g = {g0 : +U32}
  +h = {h0 : +U32}
  ((U32.add(U32.mul(a, e), U32.mul(b, g)), U32.add(U32.mul(a, f), U32.mul(b, h))), (U32.add(U32.mul(c, e), U32.mul(d, g)), U32.add(U32.mul(c, f), U32.mul(d, h))))

assert sq:
  forall +m: (+ ((U32 & U32) & (U32 & U32)) ~ Mat.copy(Pair.copy(U32.copy, U32.copy)))
  ((U32 & U32) & (U32 & U32))

def sq(m):
  mmul(m, m)

assert dig:
  forall m4: ((U32 & U32) & (U32 & U32))
  U32

def dig(m4):
  ((a, b), (c, d)) = m4
  U32.add(U32.add(U32.add(U32.mul(a, 1000), U32.mul(b, 100)), U32.mul(c, 10)), d)

assert main.out:
  U32

def main.out():
  dig(sq(sq(((1, 1), (1, 0)))))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
5332
$$ bend % --seq
5332
exit 0
$$ bend % --par
5332
exit 0
$$ bend % --js
5332
exit 0
