# audit: the bitwise operators are spelled dotted, .&. .|. .^. --
# ported from bend3 unchanged but for the Base import
import Base

assert main.out:
  U32

def main.out():
  a = 5 .&. 3   # 1
  b = 5 .|. 3   # 7
  c = 5 .^. 3   # 6
  a + 10 * b + 100 * c

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
671
$$ bend % --seq
671
exit 0
$$ bend % --par
671
exit 0
$$ bend % --js
671
exit 0
