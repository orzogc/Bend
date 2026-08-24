# The library's total-division convention at b = 0 (AUDIT 21), the Nat
# half: div answers 0, mod the DIVIDEND, so a = b * div(a,b) + mod(a,b)
# holds at every b. base_u32_divmod_zero pins the U32 rule in all four
# lanes, but the Nat rule rode unpinned: the interpreter and the C
# backend run base's Nat.divmod as written, while the JS backend wires
# the nat_divmod native (runtime.js), whose b = 0 branch no test
# reached -- gutted, BigInt division throws a RangeError and the
# compiled lane crashes where the other two answer the law. The
# nonzero legs guard the same native's ordinary division.
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

assert main.out:
  Nat

def main.out():
  Tuple{d0, m0} = Nat.divmod(7n, 0n)
  Tuple{d1, m1} = Nat.divmod(0n, 0n)
  Tuple{d2, m2} = Nat.divmod(7n, 2n)
  b0 = bu(U32.is_eq(U32.from_nat(d0), 0))
  b1 = bu(U32.is_eq(U32.from_nat(m0), 7))
  b2 = bu(U32.is_eq(U32.from_nat(d1), 0))
  b3 = bu(U32.is_eq(U32.from_nat(m1), 0))
  b4 = bu(U32.is_eq(U32.from_nat(d2), 3))
  b5 = bu(U32.is_eq(U32.from_nat(m2), 1))
  U32.to_nat(U32.add(U32.add(b0, b1), U32.add(U32.add(b2, b3), U32.add(b4, b5))))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
6n
$$ bend % --seq
6n
exit 0
$$ bend % --par
6n
exit 0
$$ bend % --js
6n
exit 0
