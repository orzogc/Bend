# λ-match sugar supports chained constructor arms, field binders, and
# default binders
# ported from bend3: the default arm's literal becomes a param (a U32
# literal shows as its Word chain)
import Base

type Foo:
  A{x: U32, y: U32}
  B{z: U32, w: U32}
  C{}

assert main:
  forall d: U32
  Foo -> U32

def main(d): \{A: x => y =>(x + y);B: z => w =>(z * w);q => d}
$$ bend % --show
main = d => \{A: (x => y => U32.add(x, y)); B: (z => w => U32.mul(z, w)); (q => d)}
