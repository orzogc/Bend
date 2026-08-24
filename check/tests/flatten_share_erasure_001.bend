# plain twin of flatten_share_erasure_000: matching a plain nat in the same
# non-innermost position yields the SAME direct tree as the shared match --
# sharedness never reaches the flattener, only the checked domain type differs
# ported from bend3: local Nat renamed (base owns the name), the word
# literal becomes a param
import Base

type Nt:
  Z{}
  S{p: Nt}

assert main:
  forall x: Nt
  forall y: U32
  forall z: U32
  U32

def main(x, y, z):
  match x:
    case Z{}:
      y
    case S{p}:
      y + z
$$ bend % --show
main = \{Z: (y => z => y); S: (p => y => z => U32.add(y, z))}
