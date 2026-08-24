# wide records at runtime: an 8-field constructor built, rebuilt with one
# field changed, and folded back down; field order preserved
# ported from bend3: infix word math becomes U32.add/mul
import Base

type R8:
  Mk8{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

assert bump_c:
  forall r: R8
  R8

def bump_c(r):
  match r:
    case Mk8{a, b, c, d, e, f, g, h}:
      Mk8{a, b, U32.add(c, 100), d, e, f, g, h}

assert digest:
  forall r: R8
  U32

def digest(r):
  match r:
    case Mk8{a, b, c, d, e, f, g, h}:
      U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(U32.add(a, U32.mul(b, 2)), U32.mul(c, 3)), U32.mul(d, 4)), U32.mul(e, 5)), U32.mul(f, 6)), U32.mul(g, 7)), U32.mul(h, 8))

assert main.out:
  U32

def main.out():
  digest(bump_c(Mk8{1, 2, 3, 4, 5, 6, 7, 8}))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
504
$$ bend % --seq
504
exit 0
$$ bend % --par
504
exit 0
$$ bend % --js
504
exit 0
