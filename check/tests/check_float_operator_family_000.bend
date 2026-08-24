# the trailing-dot arithmetic family with its precedence: *. /. bind over
# +. -. exactly as their integer twins
import Base

assert main.out:
  U32

def main.out():
  a = F32.to_u32(1.5 +. 0.25 *. 2.0)     # 2 (*. first)
  b = F32.to_u32(6.0 -. 4.0 /. 2.0)      # 4 (/. first)
  a * 10 + b

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
24
exit 0
$$ bend % --par
24
exit 0
$$ bend % --js
24
exit 0
