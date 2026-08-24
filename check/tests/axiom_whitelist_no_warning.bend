# bend3 whitelisted base's axioms and printed no !! AXIOM line for
# them; bend4's exemption IS base.bend -- its unfilled F32 asserts are
# usable silently (the assert-error rule stops at base's edge), and
# the float arithmetic answers on the compiled lanes with no warning
# text anywhere
import Base

assert main.out:
  U32

def main.out():
  F32.to_u32(1.5 +. 2.5)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend % --seq
4
exit 0
$$ bend % --par
4
exit 0
$$ bend % --js
4
exit 0
