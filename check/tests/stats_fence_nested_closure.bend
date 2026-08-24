# bend3's term_subst fence, scale layer: 32 nested add-closures in one
# body. The subst_nodes/interaction counters are gone (no --stats); the
# composed body itself carries, on base Nat, and answers zero
import Base

assert big:
  forall x1: Nat
  forall x2: Nat
  forall x3: Nat
  forall x4: Nat
  forall x5: Nat
  forall x6: Nat
  forall x7: Nat
  forall x8: Nat
  forall x9: Nat
  forall x10: Nat
  forall x11: Nat
  forall x12: Nat
  forall x13: Nat
  forall x14: Nat
  forall x15: Nat
  forall x16: Nat
  forall x17: Nat
  forall x18: Nat
  forall x19: Nat
  forall x20: Nat
  forall x21: Nat
  forall x22: Nat
  forall x23: Nat
  forall x24: Nat
  forall x25: Nat
  forall x26: Nat
  forall x27: Nat
  forall x28: Nat
  forall x29: Nat
  forall x30: Nat
  forall x31: Nat
  forall x32: Nat
  Nat

def big(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32):
  Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, Nat.add(x6, Nat.add(x7, Nat.add(x8, Nat.add(x9, Nat.add(x10, Nat.add(x11, Nat.add(x12, Nat.add(x13, Nat.add(x14, Nat.add(x15, Nat.add(x16, Nat.add(x17, Nat.add(x18, Nat.add(x19, Nat.add(x20, Nat.add(x21, Nat.add(x22, Nat.add(x23, Nat.add(x24, Nat.add(x25, Nat.add(x26, Nat.add(x27, Nat.add(x28, Nat.add(x29, Nat.add(x30, Nat.add(x31, x32)))))))))))))))))))))))))))))))

assert main.out:
  Nat

def main.out():
  big(0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))
$$ bend %
0n
$$ bend % --seq
0n
exit 0
$$ bend % --par
0n
exit 0
$$ bend % --js
0n
exit 0
