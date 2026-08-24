#[halts]
# compile_join_verdict_000's agreement law from the other walk order
# (the widest aux visited first, the 15-param failure band); bend4's
# tocl has no verdict machinery, so the threaded-f32-state loop itself
# carries -- a float guard folded into each Nat countdown arm (the
# binder-order law moves the dispatch),
# 15 F32 params, answering bend3's 7 on the compiled lanes
import Base

assert g9:
  forall n: Nat
  forall +x1: F32
  forall +x2: F32
  forall x3: F32
  forall x4: F32
  forall x5: F32
  forall x6: F32
  forall x7: F32
  forall x8: F32
  forall x9: F32
  forall x10: F32
  forall x11: F32
  forall x12: F32
  forall x13: F32
  forall x14: F32
  forall x15: F32
  F32

def g9(n, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15):
  match n:
    case Zero{}:
      if F32.is_lt(x1, 0.0):
        0.0
      else:
        x1
    case Succ{k}:
      if F32.is_lt(x1, 0.0):
        0.0
      else:
        g9(k, x1 +. x2, x2 *. 1.0, x3 *. 1.0, x4 *. 1.0, x5 *. 1.0, x6 *. 1.0, x7 *. 1.0, x8 *. 1.0, x9 *. 1.0, x10 *. 1.0, x11 *. 1.0, x12 *. 1.0, x13 *. 1.0, x14 *. 1.0, x15 *. 1.0)

assert main.out:
  U32

def main.out():
  F32.to_u32(g9(3n, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
7
exit 0
$$ bend % --par
7
exit 0
$$ bend % --js
7
exit 0
