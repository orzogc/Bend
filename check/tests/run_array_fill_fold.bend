# read-modify-write loops over a word array: fill 8 slots with squares,
# then fold them back; F32 arrays store exact f32 cells
# ported from bend3: the slab becomes Array.new(3n, 0), counters Nat;
# f32 literals are rebuilt exactly via F32.div of small integers, so
# there is no interpreter lane (Base's F32 axioms are stuck there);
# strict -- the index defs folded in, walked Nats +Nat, indexes +U32
import Base

assert wr:
  forall m: Array<U32>
  forall i: U32
  forall v: U32
  Array<U32>

def wr(m, i, v):
  (m2, old) = Array.swap(U32, m, i, v)
  m2

assert fl:
  forall n: U32
  forall d: U32
  F32

def fl(n, d):
  F32.div(U32.to_f32(n), U32.to_f32(d))

assert fill:
  forall i: Nat
  forall m: Array<U32>
  Array<U32>

def fill(i, m):
  match i:
    case 0n:
      m
    case 1n+p0:
      +p = {p0 : +Nat}
      +j = {U32.from_nat(p) : +U32}
      fill(p, wr(m, j, U32.mul(j, j)))

assert total:
  forall i: Nat
  forall m: Array<U32>
  forall acc: U32
  U32

def total(i, m, acc):
  match i:
    case 0n:
      acc
    case 1n+p0:
      +p = {p0 : +Nat}
      (m2, v) = Array.get(m, U32.from_nat(p))
      total(p, m2, U32.add(acc, v))

assert fsum:
  U32

def fsum():
  F32.to_u32(F32.mul(F32.add(fl(3, 2), fl(9, 4)), fl(100, 1)))

assert main.out:
  U32

def main.out():
  U32.add(U32.mul(total(8n, fill(8n, Array.new(3n, 0)), 0), 1000), fsum())

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
140375
exit 0
$$ bend % --par
140375
exit 0
$$ bend % --js
140375
exit 0
