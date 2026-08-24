# the displaced element: Array.swap moves the old value out beside the
# written array -- bend4's affine respell of bend3's Set-moves-old law
# (the a[i] <- v sugar rides Array.set and drops the old element; swap
# is the keeping form). the moved-out word shares via +
import Base

assert main.out:
  U32

def main.out():
  (b, old0) = Array.swap(U32, Array.new(1n, 5), 0, 1)
  +old = {old0 : +U32}
  (b1, x) = b[0]
  old + old + x

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
11
$$ bend % --seq
11
exit 0
$$ bend % --par
11
exit 0
$$ bend % --js
11
exit 0
