# Rand is a pure linear token: seeded once, next/range thread it and are
# fully deterministic on every executor
# ported from bend3: bend-base Rand (xorshift32, zero seed remapped to
# 2654435769) is inlined; the full-word mods keep this off the
# interpreter (unary Nat division there is astronomic); strict -- the
# mix chain rides annotated +U32 rebinds, the continuation defs fold
# into sequential destructures
import Base

type Rnd:
  Rnd{state: U32}

assert rnew:
  forall +seed: +U32
  Rnd

def rnew(seed):
  match U32.is_zero(seed):
    case True{}:
      Rnd{2654435769}
    case False{}:
      Rnd{seed}

assert rnext:
  forall r: Rnd
  (Rnd & U32)

def rnext(r):
  match r:
    case Rnd{s0}:
      +s = {s0 : +U32}
      +a = {U32.xor(s, U32.shln(13n, s)) : +U32}
      +b = {U32.xor(a, U32.shrn(17n, a)) : +U32}
      +c = {U32.xor(b, U32.shln(5n, b)) : +U32}
      (Rnd{c}, c)

assert rrange:
  forall r: Rnd
  forall n: U32
  (Rnd & U32)

def rrange(r, n):
  (r2, x) = rnext(r)
  (r2, U32.mod(x, n))

assert go:
  forall r: Rnd
  U32

def go(r):
  (r1, a) = rnext(r)
  (r2, b) = rnext(r1)
  (r3, c) = rrange(r2, 10)
  U32.add(U32.add(U32.mul(U32.mod(a, 1000), 10000), U32.mul(U32.mod(b, 1000), 10)), c)

assert main.out:
  U32

def main.out():
  go(rnew(42))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
4323489
exit 0
$$ bend % --par
4323489
exit 0
$$ bend % --js
4323489
exit 0
