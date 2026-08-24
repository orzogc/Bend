# float literals: D.D desugars to F32.div(U32.to_f32(digits),
# U32.to_f32(scale)) -- correctly-rounded for exact operands. no float
# TEXT exists (F32.show/read are ruled out): the readback rides
# F32.to_u32; base's F32 axioms are live strict (base-native)
import Base

assert main.out:
  U32

def main.out():
  a = F32.to_u32(1.5 *. 2.0)             # 3
  b = F32.to_u32(0.25 +. 2.75)           # 3
  c = F32.to_u32(10.0 /. 4.0)            # 2 (2.5 truncates)
  a + 10 * b + 100 * c

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
233
exit 0
$$ bend % --par
233
exit 0
$$ bend % --js
233
exit 0
