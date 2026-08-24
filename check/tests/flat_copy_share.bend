#[halts]
# an all-word record used twice as constructor fields AND read after:
# every use of the words-held value must own its instance (a shared
# box double-frees), and a copy of words is the words. 16-instead-of
# -18 was the shared-box failure.
# ported from bend3: f32 literals rebuild via U32.to_f32 (bend4 has
# no float literal), the reused record takes a + binder, and the pair
# rides through a def (a literal ctor may not be destructured in
# place); no interp lane (Base's F32 axioms are stuck there)
import Base

type V3:
  Vec{x: F32, y: F32, z: F32}

type Two:
  Tw{a: V3, b: V3}

assert vsum:
  forall v: V3
  F32

def vsum(v):
  Vec{x, y, z} = v
  F32.add(F32.add(x, y), z)

assert pair:
  forall +p: V3
  Two

def pair(p):
  Tw{p, p}

assert main.out:
  U32

def main.out():
  +p = {Vec{U32.to_f32(1), U32.to_f32(2), U32.to_f32(3)} : V3}
  Tw{a, b} = pair(p)
  F32.to_u32(F32.add(F32.add(vsum(a), vsum(b)), vsum(p)))

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
18
exit 0
$$ bend % --par
18
exit 0
$$ bend % --js
18
exit 0
