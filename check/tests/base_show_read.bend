# number <-> text: U32.show/read round trips (through U32.MAX), and
# read rejects junk
# ported from bend3: U32.read answers Maybe<U32> (no Parser module),
# so rejection reads None; the F32.show half is dropped (bend4 has no
# float text); the interp lane is dropped (the evaluator has no u32
# natives, so U32.MAX's show cannot reduce there)
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert rd:
  forall s: String
  U32

def rd(s):
  match U32.read(s):
    case Some{v}:
      v
    case None{}:
      999

assert main.out:
  U32

def main.out():
  b0 = bu(String.eq(U32.show(4242), "4242"))
  b1 = bu(String.eq(U32.show(0), "0"))
  b2 = bu(U32.is_eq(rd("123"), 123))
  b3 = bu(U32.is_eq(rd(U32.show(4294967295)), 4294967295))
  b4 = bu(U32.is_eq(rd("x"), 999))
  U32.add(U32.add(U32.add(U32.add(b0, b1), b2), b3), b4)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
5
exit 0
$$ bend % --par
5
exit 0
$$ bend % --js
5
exit 0
