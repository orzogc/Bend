# Nat.div(n, 2n) is not a structural subterm of n: the loop terminates
# at runtime, but the descent judgment refuses it (bend has no opt-out, so the
# runnable half of the bend3 test has no place in this file).
# ported from bend3: U32 halving becomes Nat.div
import Base

law Nat.div:
  for a: Nat
  for b: Nat
  Nat

law Nat.div.fin:
  for qr: Nat & Nat
  Nat

def Nat.div.fin(qr):
  (q, r) = qr
  q

def Nat.div(a, b):
  Nat.div.fin(Nat.divmod(a, b))

law fold:
  for n: Nat
  Nat

def fold(n):
  match n:
    case 0n:
      0n
    case n:
      1n+ fold(Nat.div(n, 2n))

law main:
  Nat

def main(): fold(10n)

#|Error:
#|- expected : a decreasing self-call (some live argument must shrink)
#|- observed : fold
#|Context:
#|- n : Nat<> - Zero{}
#|Location: fold
#|31 |     case n:
#|32>|       1n+ fold(Nat.div(n, 2n))
#|33 |
#|exit 1
