# a ref-partial closure with an erased remaining param: dynamic callers
# feed every source arg (erased included) through the stored value
# ported from bend3
import Base

assert kf.go:
  forall -n: U32
  forall x: U32
  U32

def kf.go(n, x):
  x

assert kf:
  @-n: U32 -> U32 -> U32

def kf():
  kf.go

type BoxK:
  MkBoxK{f: @-n: U32 -> U32 -> U32}

assert use:
  forall b: BoxK
  U32

def use(b):
  match b:
    case MkBoxK{f}:
      f(9, 3)

assert main.out:
  U32

def main.out():
  use(MkBoxK{kf})

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
3
$$ bend % --seq
3
exit 0
$$ bend % --par
3
exit 0
$$ bend % --js
3
exit 0
