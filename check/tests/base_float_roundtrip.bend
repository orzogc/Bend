# the trailing-dot float family round-trips through arithmetic: literals
# build exact halves, -. and /. undo +. and *. -- readback via
# F32.to_u32 (no float text in bend4, by ruling)
import Base

assert main.out:
  U32

def main.out():
  x = 6.25 -. 2.25                        # 4.0
  y = 3.5 *. 2.0 /. 0.5                  # 14.0 (left assoc)
  F32.to_u32(x) + F32.to_u32(y) * 10

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
144
exit 0
$$ bend % --par
144
exit 0
$$ bend % --js
144
exit 0
