# array statements: read `(m, x) = a[i]` and write `m = a[i] <- v` as
# bend4 spells them (the read rides the array back beside the element,
# and a destructure heads its statement)
# ported from bend3: no array literal exists (Array.new), word literals
# become params
import Base

assert main:
  forall i: U32
  forall j: U32
  forall k: U32
  forall v: U32
  forall w: U32
  U32

def main(i, j, k, v, w):
  (m2, x) = Array.new(2n, v)[i]
  (m4, z) = (m2[j] <- w)[k]
  x + z
$$ bend % --show
main = i => j => k => v => w => \{Tuple: (m2 => x => \{Tuple: (m4 => z => U32.add(x, z))}(Array.get(Array.set(m2, j, w), k)))}(Array.get(Array.new(2n, v), i))
