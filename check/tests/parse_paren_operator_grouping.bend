# parentheses regroup operator chains against their native
# associativity and precedence -- ported from bend3
import Base

assert main.out:
  U32

def main.out():
  a = 10 - (2 - 1)        # 9 (native left-assoc reads 10-2-1 = 7)
  b = (2 + 3) * 4         # 20 (native * over +)
  c = 6 .&. (3 .|. 4)     # 6 (native .&. over .|.)
  a + b * 10 + c * 1000

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
6209
$$ bend % --seq
6209
exit 0
$$ bend % --js
6209
exit 0
