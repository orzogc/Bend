# the recursive spelling meets the shift, on Word directly (the ruled
# port of bend3's div2 = x >> 1 hom route: no axiom roster, no unary
# crossing -- bend3's 0/1/2+p div2 IS base's Nat.half ladder, and the
# theorem is the width-generic shr_half): a right shift drops the low
# bit and pads a zero on top, so its value is the half -- each arm is
# base's Word.shr.pad_to_nat spliced to Nat.half_double(_succ) by one
# trans. The U32 face instantiates it at 32 bits, and div2 (half
# through the readback) carries the runtime.
# ported from bend3: main keeps the golden 87; the mod operand shrinks
# from U32.MAX to 195 (same residue: U32.mod rides the unary Nat
# divmod, and a 2^32 unary walk has no budget in any lane)
import Base

assert Nat.half:
  forall m: Nat
  Nat

def Nat.half(m):
  match m:
    case 0n:
      0n
    case 1n:
      0n
    case 2n+r:
      1n+Nat.half(r)

assert Nat.half_double:
  forall m: Nat
  {Nat.half(Nat.double(m)) == m : Nat}

def Nat.half_double(m):
  match m:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.half(Nat.double(q)), q, Nat.half_double(q))

assert Nat.half_double_succ:
  forall m: Nat
  {Nat.half(1n+Nat.double(m)) == m : Nat}

def Nat.half_double_succ(m):
  match m:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.half(1n+Nat.double(q)), q, Nat.half_double_succ(q))

assert Word.shr.pad_to_nat:
  forall n: Nat
  forall w: Word(n)
  {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}

def Word.shr.pad_to_nat(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+q:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Nat, Nat, y => Nat.double(y), Word.to_nat(1n+q, Word.shr.pad(q, t)), Word.to_nat(q, t), Word.shr.pad_to_nat(q, t))
        case WCon{True{}, t}:
          Equal.cong(Nat, Nat, y => 1n+Nat.double(y), Word.to_nat(1n+q, Word.shr.pad(q, t)), Word.to_nat(q, t), Word.shr.pad_to_nat(q, t))

assert shr_half:
  forall +n: +Nat
  forall +w: + Word(n) ~ Word.copy(n)
  {Word.to_nat(n, Word.shr(n, w)) == Nat.half(Word.to_nat(n, w)) : Nat}

def shr_half(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.trans(Nat, Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), Nat.half(Nat.double(Word.to_nat(p, t))), Word.shr.pad_to_nat(p, t), Equal.sym(Nat, Nat.half(Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), Nat.half_double(Word.to_nat(p, t))))
        case WCon{True{}, t}:
          Equal.trans(Nat, Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), Nat.half(1n+Nat.double(Word.to_nat(p, t))), Word.shr.pad_to_nat(p, t), Equal.sym(Nat, Nat.half(1n+Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), Nat.half_double_succ(Word.to_nat(p, t))))

assert u32_shr_half:
  forall +a: +U32
  {U32.to_nat(U32.shr(a)) == Nat.half(U32.to_nat(a)) : Nat}

def u32_shr_half(a):
  match a:
    case U32{w}:
      shr_half(32n, w)

assert div2:
  forall a: U32
  U32

def div2(a):
  U32.from_nat(Nat.half(U32.to_nat(a)))

assert main.out:
  U32

def main.out():
  (div2(9) * 10) + div2(U32.mod(195, 100))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
87
$$ bend % --seq
87
exit 0
$$ bend % --par
87
exit 0
$$ bend % --js
87
exit 0
