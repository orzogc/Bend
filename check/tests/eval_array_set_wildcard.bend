# the binderless set: a[i] <- v is a TERM answering the written array,
# so bend3's wildcard statement form is just an expression feeding the
# next read -- the displaced element is dropped by Array.set
import Base

assert main.out:
  U32

def main.out():
  (a2, x) = ((Array.new(2n, 0)[0] <- 3)[1] <- 4)[0]
  (a3, y) = a2[1]
  x * 10 + y

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
34
$$ bend % --seq
34
exit 0
$$ bend % --js
34
exit 0
