# bend4 has no float printer: an F32 is not C-showable and the interp
# keeps its stuck build -- the value reads back through F32.to_u32 and
# the trailing-dot comparisons (F32.is_lt is the one compiled comparison)
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  if b: 1 else: 0

assert main.out:
  U32

def main.out():
  half = 0.5
  F32.to_u32(100.25) * 10 + bu(half <. 1.0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
1001
exit 0
$$ bend % --par
1001
exit 0
$$ bend % --js
1001
exit 0
