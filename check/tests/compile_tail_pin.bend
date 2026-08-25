# Witness for Mask's protocol pin (Mint.tail).
#
# side binds big(a) to x and never reads it. Carbonize cuts there and
# mints side$k0 over the captured b AND the discarded result x, and x
# has zero uses. Mask erases unused minted parameters, so without the
# tail pin it would erase x -- and a seq continuation takes its LAST
# parameter from res, so b would inherit the res slot and read the
# result of big(a) instead of the b the frame carried.
#
# No bench discards a call's result, so this path is otherwise
# untested. Expect 3n: big is the identity on Nat, and side answers
# big(b).

import Base

assert big:
  forall n: Nat
  Nat

def big(n):
  match n:
    case 0n:
      0n
    case 1n+p:
      Succ{big(p)}

assert side:
  forall a: Nat
  forall b: Nat
  Nat

def side(a, b):
  x = big(a)
  big(b)

assert main.out:
  Nat

def main.out():
  side(5n, 3n)

assert main:
  IO(Unit)

def main():
  IO.print(String.append(Nat.show(main.out()), "n"))

$$ bend %
3n
$$ bend % --seq
3n
exit 0
$$ bend % --par
3n
exit 0
$$ bend % --js
3n
exit 0
