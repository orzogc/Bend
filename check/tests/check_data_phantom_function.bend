# refusal pin: bend3's phantom-param narrowing demanded every TYPE
# argument of a saturated datatype be Data at a copy site, rejecting
# use(s) + use(s) over Box(Wrap(U32 -> U32)). bend4 has no Data kind to
# bound a param with -- sharing is the + quantity, phantom or not -- so
# the faithful translation dies on the Data spelling in Box4's head.
# ported from bend3: ctor names bare and unique; the nested matches
# would route through helper defs, never reached here
import Base

type Tag2<T: Type>:
  MkTag2{}
type Wrap2<T: Type>:
  MkWrap2{g: Tag2<T>}
type Box4<T: Data>:
  MkBox4{v: T}

assert use:
  forall x: Box4<Wrap2<U32 -> U32>>
  U32

def use(x):
  match x:
    case MkBox4{w}:
      use.go(w)

assert use.go:
  forall w: Wrap2<U32 -> U32>
  U32

def use.go(w):
  match w:
    case MkWrap2{g}:
      use.fin(g)

assert use.fin:
  forall g: Tag2<U32 -> U32>
  U32

def use.fin(g):
  match g:
    case MkTag2{}:
      1

assert main:
  U32

def main():
  s = {MkBox4{MkWrap2{MkTag2{}}} : Box4<Wrap2<U32 -> U32>>}
  use(s) + use(s)
$$ bend %
Error:
- expected : a defined name
- observed : Data
Location:
13 |   MkWrap2{g: Tag2<T>}
14>| type Box4<T: Data>:
15 |   MkBox4{v: T}
