# the sugar program's surface in one book: infix arithmetic and
# bitwise (dotted) and logical operators, shifts, comparisons,
# if/elif/else, list literals and cons and ++, array read/write, and
# the fork-let -- floats keep their own family (stuck in the interp).
# a re-tested binder rides + (affine core), a fork after a plain let
# needs the let's ';' (the & would read as a Pair type)
import Base

assert String.length:
  forall s: String
  Nat

def String.length(s):
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+String.length(t)

assert cmp:
  forall x0: U32
  U32

def cmp(x0):
  +x = {x0 : +U32}
  if x < 3: 100 elif x < 6: 200 else: 300

assert getat:
  forall a: Array<U32>
  forall i: U32
  U32

def getat(a, i):
  (a2, got) = a[i]
  got

assert csum:
  forall xs: List<U32>
  forall acc: U32
  U32

def csum(xs, acc):
  match xs:
    case Con{h, t}:
      csum(t, 10 * acc + h)
    case Nil{}:
      acc

assert main.out:
  U32

def main.out():
  arr = Array.new(2n, 0);
  & x : U32 = cmp(1) & y : U32 = cmp(9);
  a = 2 + 3 * 4
  b = 1 << 3n
  c = 6 .&. 3 .|. 8 .^. 12
  d = csum([1, 2, 7 - 4], 0)
  s = "ab" ++ "cd"
  g = getat(arr[1] <- 5, 1)
  a + b + c + d + (if 20 < 8 || True{} && False{}: 1 else: 2) + U32.from_nat(String.length(s)) + x + y + g

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
562
$$ bend % --seq
562
exit 0
$$ bend % --par
562
exit 0
$$ bend % --js
562
exit 0
