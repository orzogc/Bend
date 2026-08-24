# f32: a single-f32-field ctor and f32 array elements move by swap
# ported from bend3: the [:F32] literal becomes an explicit 4-leaf
# tree, gets become swaps, literals rebuild via F32.div; no
# interpreter lane (Base's F32 axioms are stuck there)
import Base

type FBx:
  MkFBx{x: F32}

assert fl:
  forall n: U32
  forall d: U32
  F32

def fl(n, d):
  F32.div(U32.to_f32(n), U32.to_f32(d))

assert unbox:
  forall b: FBx
  F32

def unbox(b):
  match b:
    case MkFBx{x}:
      x

assert main.out:
  U32

def main.out():
  (b2, x) = Array.swap(F32, ANode{ANode{ALeaf{U32.to_f32(0)}, ALeaf{fl(5, 4)}}, ANode{ALeaf{U32.to_f32(0)}, ALeaf{U32.to_f32(0)}}}, 2, U32.to_f32(0))
  (b3, z) = Array.swap(F32, b2, 0, U32.to_f32(0))
  F32.to_u32(F32.mul(F32.add(x, F32.add(unbox(MkFBx{fl(5, 2)}), z)), fl(100, 1)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
375
exit 0
$$ bend % --par
375
exit 0
$$ bend % --js
375
exit 0
