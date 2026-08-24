# tuples end to end: (a,b) values (right-nested), tuple destructuring
# in defs and match arms, type-level (A & B) and &x:A -> B, and a
# generic swap through the dependent Pair -- pure, so the compiled
# lanes cover the Tuple ctor through the C backend too.
# ported from bend3: literal tuple patterns (case (4, 3)) become a
# destructure plus U32.is_eq checks (bend4 has no word patterns);
# result 118 (bend3's golden) shown as a Nat
import Base

assert swap:
  forall -A: Type
  forall -B: Type
  forall p: (A & B)
  (B & A)

def swap(A, B, p):
  (a, b) = p
  (b, a)

assert dep:
  forall p: &x:U32 -> (U32 & U32)
  U32

def dep(p):
  (x, y, z) = p
  U32.add(U32.add(x, y), z)

assert check:
  forall q: (U32 & U32)
  U32

def check(q):
  (qa, qb) = q
  match Bool.and(U32.is_eq(qa, 4), U32.is_eq(qb, 3)):
    case True{}:
      U32.add(100, dep((5, 6, 7)))
    case False{}:
      0

assert main.out:
  Nat

def main.out():
  U32.to_nat(check(swap(U32, U32, (3, 4))))

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
118n
$$ bend % --seq
118n
exit 0
$$ bend % --par
118n
exit 0
$$ bend % --js
118n
exit 0
