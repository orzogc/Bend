# the trailing-dot comparison family at the comparison level: <. ranks with
# < (F32.is_lt is the one comparison the C emitter carries; the rest
# are pinned yellow by run_float_specials)
import Base

assert bu:
  forall b: Bool
  U32

def bu(b):
  if b: 1 else: 0

assert main.out:
  U32

def main.out():
  a = bu(0.5 <. 1.5)                      # 1
  b = bu(2.5 <. 0.5 +. 1.0)              # 0 (+. first: 2.5 < 1.5)
  a * 10 + b

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
10
exit 0
$$ bend % --js
10
exit 0
