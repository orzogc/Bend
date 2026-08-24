# CONFLUENCE of copies under real threads: ONE list over-used by four
# fork siblings at once, each folding with a different salt -- the
# checksum is identical in the interpreter, at one thread and at eight
# (verified against an independent host-JS mirror: 2827519320).
# ported from bend3: the builder takes Nat fuel with a +U32 mirror,
# forks spell the Par<> Both destructure, the shared list and reused
# words take + Cop binders (base witnesses, a local L.copy),
# operators spell U32.xor/mul/add
import Base

type L:
  LC{h: U32, t: L}
  LN{}

assert L.copy:
  forall t: L
  Copy(L, t) & Copy(L, t)

def L.copy(t):
  match t:
    case LC{h, t}:
      ((hx, he), (hy, hf)) = U32.copy(h)
      ((tx, te), (ty, tf)) = L.copy(t)
      s10 = Equal.cong(U32, L, z => LC{z, t}, h, hx, he)
      s11 = Equal.cong(L, L, z => LC{hx, z}, t, tx, te)
      t11 = Equal.trans(L, LC{h, t}, LC{hx, t}, LC{hx, tx}, s10, s11)
      s20 = Equal.cong(U32, L, z => LC{z, t}, h, hy, hf)
      s21 = Equal.cong(L, L, z => LC{hy, z}, t, ty, tf)
      t21 = Equal.trans(L, LC{h, t}, LC{hy, t}, LC{hy, ty}, s20, s21)
      ((LC{hx, tx}, t11), (LC{hy, ty}, t21))
    case LN{}:
      ((LN{}, {==}), (LN{}, {==}))

assert mk:
  forall n: Nat
  forall +m: +U32
  L

def mk(n, m):
  match n:
    case 0n:
      LN{}
    case 1n+p:
      LC{U32.mul(m, 2654435761), mk(p, U32.sub(m, 1))}

assert fold:
  forall xs: L
  forall salt: U32
  U32

def fold(xs, salt):
  match xs:
    case LN{}:
      salt
    case LC{h, t}:
      fold(t, U32.add(U32.mul(U32.xor(salt, h), 31), 7))

assert burst:
  forall +xs: +L
  U32

def burst(xs):
  Both{a, Both{b, Both{c, d}}} = {Both{fold(xs, 1), Both{fold(xs, 2), Both{fold(xs, 3), fold(xs, 4)}}} : Par<U32, Par<U32, Par<U32, U32>>>}
  U32.add(U32.add(U32.add(a, U32.mul(b, 3)), U32.mul(c, 7)), U32.mul(d, 11))

assert main.out:
  U32

def main.out():
  xs = mk(24n, 24)
  burst(xs)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
2827519320
$$ bend % --seq
2827519320
exit 0
$$ bend % --par
2827519320
exit 0
$$ bend % --js
2827519320
exit 0
