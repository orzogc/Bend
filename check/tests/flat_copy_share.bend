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

# copy witness for the shared record: never emitted, only licenses +V3
assert V3.copy:
  forall v: V3
  Copy(V3, v) & Copy(V3, v)

def V3.copy(v):
  match v:
    case Vec{x, y, z}:
      ((x1, ex1), (x2, ex2)) = F32.copy(x)
      ((y1, ey1), (y2, ey2)) = F32.copy(y)
      ((z1, ez1), (z2, ez2)) = F32.copy(z)
      p1 = Equal.trans(V3, Vec{x, y, z}, Vec{x1, y, z}, Vec{x1, y1, z1},
                       Equal.cong(F32, V3, w => Vec{w, y, z}, x, x1, ex1),
                       Equal.trans(V3, Vec{x1, y, z}, Vec{x1, y1, z}, Vec{x1, y1, z1},
                                   Equal.cong(F32, V3, w => Vec{x1, w, z}, y, y1, ey1),
                                   Equal.cong(F32, V3, w => Vec{x1, y1, w}, z, z1, ez1)))
      p2 = Equal.trans(V3, Vec{x, y, z}, Vec{x2, y, z}, Vec{x2, y2, z2},
                       Equal.cong(F32, V3, w => Vec{w, y, z}, x, x2, ex2),
                       Equal.trans(V3, Vec{x2, y, z}, Vec{x2, y2, z}, Vec{x2, y2, z2},
                                   Equal.cong(F32, V3, w => Vec{x2, w, z}, y, y2, ey2),
                                   Equal.cong(F32, V3, w => Vec{x2, y2, w}, z, z2, ez2)))
      ((Vec{x1, y1, z1}, p1), (Vec{x2, y2, z2}, p2))

assert vsum:
  forall v: V3
  F32

def vsum(v):
  Vec{x, y, z} = v
  F32.add(F32.add(x, y), z)

assert pair:
  forall +p: +V3
  Two

def pair(p):
  Tw{p, p}

assert main.out:
  U32

def main.out():
  +p = {Vec{U32.to_f32(1), U32.to_f32(2), U32.to_f32(3)} : +V3}
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
