# infix operators: bend3's ladder in bend4's dialect, loosest to
# tightest: || over && over < <= > over .|. over .^. over .&. over
# << >> over + - over * /; value ops left-assoc, <> ++ right-assoc.
# == != % are out: the Eql brace form owns ==/!= and % heads a rewrite
# (value equality is U32.is_eq); float twins ride a trailing dot, pinned by the
# float family. shift counts are Nat literals (U32.shln's own law).
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  if b: 1 else: 0

assert main.out:
  U32

def main.out():
  a = 2 + 3 * 4              # 14  (* over +)
  b = 2 + 2 << 1n            # 8   (+ over <<)
  c = 6 .&. 3 << 1n          # 6   (<< over .&.)
  d = 4 .^. 6 .&. 3          # 6   (.&. over .^.)
  e = 1 .|. 6 .^. 4          # 3   (.^. over .|.)
  f = bu(3 <= 1 .|. 2)       # 1   (.|. over <=)
  g = bu(True{} && False{} || True{})  # 1 (&& over ||)
  h = 10 - 2 - 3             # 5   (left assoc)
  a + b + c + d + e + f + g + h

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
44
$$ bend % --seq
44
exit 0
$$ bend % --par
44
exit 0
$$ bend % --js
44
exit 0
