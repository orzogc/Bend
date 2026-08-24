# the write-headed twin of compile_let_headed_app: an eta-short arm
# heading in an array write statement, tailing the self-recursive
# call -- the saturating application commutes through the statement
# ported from bend3: the [:U32] set becomes Array.swap, the counter a Nat
import Base

assert go:
  forall +f: +Nat
  forall data: Array<U32>
  U32 -> U32

def go(f, data):
  match f:
    case 0n:
      x => x
    case 1n+g:
      (d2, z) = Array.swap(U32, data, 0, U32.add(1, U32.from_nat(g)))
      go(g, d2)

assert main.out:
  U32

def main.out():
  go(3n, ALeaf{0})(7)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
7
$$ bend % --seq
7
exit 0
$$ bend % --par
7
exit 0
$$ bend % --js
7
exit 0
