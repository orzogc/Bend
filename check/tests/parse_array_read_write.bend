# array read/write syntax over base Array ops: a[i] is Array.get(a, i)
# (leftovers-first, the array rides back beside the element) and
# a[i] <- v is Array.set(a, i, v). bend3's bare-statement error census
# has no counterpart wall: both forms are plain terms here
import Base

assert main.out:
  U32

def main.out():
  (a2, x) = (Array.new(2n, 7)[1] <- 9)[1]
  (a3, y) = a2[0]
  x * 10 + y

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
97
$$ bend % --seq
97
exit 0
$$ bend % --par
97
exit 0
$$ bend % --js
97
exit 0
