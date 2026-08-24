# single-precision rounding law: 0.1 +. 0.2 rounds to exactly the
# f32 of 0.3 (0x3E99999A both ways), unlike the double-precision folk
# inequality -- neither side is less
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  if b: 1 else: 0

assert main.out:
  U32

def main.out():
  bu(0.1 +. 0.2 <. 0.3) + bu(0.3 <. 0.1 +. 0.2)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
0
exit 0
$$ bend % --par
0
exit 0
$$ bend % --js
0
exit 0
