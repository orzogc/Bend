# flat records at every width: 3/4/8-field records, a right-nested
# tuple, an f32 field, a whole-record forward, and a recursive def
# returning a wide record
# ported from bend3: shares become +params, f32 literals rebuild via
# U32.to_f32; no interpreter lane (Base's F32 axioms are stuck there)
import Base

type S3:
  MkS3{a: U32, b: U32, c: U32}

type S4:
  MkS4{a: U32, b: U32, c: U32, d: U32}

type S8:
  MkS8{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

type FM:
  MkFM{a: U32, x: F32}

assert mk3:
  forall +x: +U32
  S3

def mk3(x):
  MkS3{x, U32.add(x, 1), U32.add(x, 2)}

assert sum3:
  forall s: S3
  U32

def sum3(s):
  MkS3{a, b, c} = s
  U32.add(U32.add(a, b), c)

assert fwd3:
  forall s: S3
  U32

def fwd3(s):
  sum3(s)

assert mk8:
  forall +x: +U32
  S8

def mk8(x):
  MkS8{x, U32.add(x, 1), U32.add(x, 2), U32.add(x, 3), U32.add(x, 4), U32.add(x, 5), U32.add(x, 6), U32.add(x, 7)}

assert sum8:
  forall s: S8
  U32

def sum8(s):
  MkS8{a, b, c, d, e, f, g, h} = s
  U32.add(U32.add(U32.add(a, b), U32.add(c, d)), U32.add(U32.add(e, f), U32.add(g, h)))

assert tup3:
  forall +x: +U32
  U32 & U32 & U32

def tup3(x):
  (x, U32.mul(x, 2), U32.mul(x, 3))

assert rec4:
  forall +n: +Nat
  S4

def rec4(n):
  match n:
    case 0n:
      MkS4{1, 2, 3, 4}
    case 1n+p:
      MkS4{a, b, c, d} = rec4(p)
      MkS4{U32.add(b, 1), U32.add(c, 1), U32.add(d, 1), U32.add(a, U32.add(1, U32.from_nat(p)))}

assert fmix:
  forall x: U32
  FM

def fmix(x):
  MkFM{x, U32.to_f32(3)}

assert main.out:
  U32

def main.out():
  (ta, tb, tc) = tup3(7)
  MkS4{ra, rb, rc, rd} = rec4(5n)
  MkFM{fa, fx} = fmix(9)
  s3 = fwd3(mk3(10))
  s8 = sum8(mk8(100))
  U32.add(U32.add(s3, s8), U32.add(U32.add(U32.add(ta, tb), tc), U32.add(U32.add(U32.add(U32.add(ra, rb), U32.add(rc, rd)), fa), F32.to_u32(fx))))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
955
exit 0
$$ bend % --par
955
exit 0
$$ bend % --js
955
exit 0
