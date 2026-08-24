# two spellings of one float meet bit-for-bit: 2.5 and 5.0 /. 2.0 are
# the same F32, so neither is less than the other (F32.is_lt is the
# compiled comparison; is_eq stays on the run_float_specials yellow)
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  if b: 1 else: 0

assert main.out:
  U32

def main.out():
  bu(2.5 <. 5.0 /. 2.0) + bu(5.0 /. 2.0 <. 2.5)

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
