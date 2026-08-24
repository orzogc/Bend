# the left-shift roster, on bend4's own law (the ruled port of bend3's
# 5-bit count mask kit: bend4's U32.shln takes a Nat count and shifts
# OUT past the width -- no mask exists, run_word_shifts verified it,
# and here it is pinned as theorems): the one-step hom is definitional
# (shln(1) IS shl), composition holds at ANY counts by base's
# U32.shln_add -- the very law bend3's mask refuted at 16+16 -- the
# open-count low bit is even (base's U32.shl_even), and the mask edges
# invert: 32 and 33 shift to zero, proved closed by plain reduction.
# ported from bend3: main carries run_word_shifts' battery -- the five
# in-range pins agree across dialects, the three mask-edge pins re-pin
# to bend4's shift-out (1<<32 = 0 where bend3's mask said 1) -- and the
# golden 8 carries; bend3's masked main (65) has no bend4 value
import Base

assert Nat.even:
  forall m: Nat
  Bool

def Nat.even(m):
  match m:
    case 0n:
      True{}
    case 1n:
      False{}
    case 2n+r:
      Nat.even(r)

assert Nat.even_double:
  forall m: Nat
  {Nat.even(Nat.double(m)) == True{} : Bool}

def Nat.even_double(m):
  match m:
    case 0n:
      {==}
    case 1n+q:
      Nat.even_double(q)

assert U32.shln_add:
  forall k: Nat
  forall m: Nat
  forall a: U32
  {U32.shln(k, U32.shln(m, a)) == U32.shln(Nat.add(m, k), a) : U32}

def U32.shln_add(k, m, a):
  match m:
    case 0n:
      {==}
    case 1n+q:
      U32.shln_add(k, q, U32.shl(a))

assert U32.shl_even.go:
  forall w: Word(32n)
  {Nat.even(Word.to_nat(32n, Word.shl(32n, w))) == True{} : Bool}

def U32.shl_even.go(w):
  match w:
    case WCon{b, t}:
      Nat.even_double(Word.to_nat(31n, Word.shl.put(31n, b, t)))

assert U32.shl_even:
  forall a: U32
  {Nat.even(U32.to_nat(U32.shl(a))) == True{} : Bool}

def U32.shl_even(a):
  match a:
    case U32{w}:
      U32.shl_even.go(w)

assert shl_hom_one:
  forall a: U32
  {U32.shln(1n, a) == U32.shl(a) : U32}

def shl_hom_one(a):
  {==}

assert shln_compose:
  forall a: U32
  {U32.shln(16n, U32.shln(16n, a)) == U32.shln(32n, a) : U32}

def shln_compose(a):
  U32.shln_add(16n, 16n, a)

assert shln_low_bit:
  forall a: U32
  {Nat.even(U32.to_nat(U32.shln(1n, a))) == True{} : Bool}

def shln_low_bit(a):
  U32.shl_even(a)

assert shl32_gone:
  {U32.shln(32n, 5) == 0 : U32}

def shl32_gone():
  {==}

assert shl33_gone:
  {U32.shln(33n, 3) == 0 : U32}

def shl33_gone():
  {==}

assert bu:
  forall b: Bool
  U32

def bu(b):
  match b:
    case False{}:
      0
    case True{}:
      1

assert main.out:
  U32

def main.out():
  b0 = bu(U32.is_eq(1 << 31n, 2147483648))
  b1 = bu(U32.is_eq(1 << 32n, 0))
  b2 = bu(U32.is_eq(3 << 31n, 2147483648))
  b3 = bu(U32.is_eq(2147483648 >> 31n, 1))
  b4 = bu(U32.is_eq(2147483648 >> 32n, 0))
  b5 = bu(U32.is_eq(5 >> 33n, 0))
  b6 = bu(U32.is_eq(4294967295 << 28n, 4026531840))
  b7 = bu(U32.is_eq(1 << 0n, 1))
  ((((((b0 + b1) + b2) + b3) + b4) + b5) + b6) + b7

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
8
$$ bend % --seq
8
exit 0
$$ bend % --par
8
exit 0
$$ bend % --js
8
exit 0
