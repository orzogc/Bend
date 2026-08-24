# f32: dynamic accumulation (exact ops feed an integer digest)
# ported from bend3: f32 literals rebuild via F32.div of integers, the
# counter walks a Nat; no interpreter lane (F32 axioms are stuck there)
import Base

assert fl:
  forall n: U32
  forall d: U32
  F32

def fl(n, d):
  F32.div(U32.to_f32(n), U32.to_f32(d))

assert loop:
  forall +n: +Nat
  forall acc: F32
  F32

def loop(n, acc):
  match n:
    case 0n:
      acc
    case 1n+p:
      loop(p, F32.add(acc, F32.mul(U32.to_f32(U32.add(1, U32.from_nat(p))), fl(1, 2))))

assert main.out:
  U32

def main.out():
  F32.to_u32(F32.mul(loop(10n, fl(1, 4)), fl(100, 1)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
2775
exit 0
$$ bend % --par
2775
exit 0
$$ bend % --js
2775
exit 0
