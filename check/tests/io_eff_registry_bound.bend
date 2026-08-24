# io (io_eff_registry_bound): the effect registry holds IO_EFFS = 64
# rows and every row is usable. This program's companion pads the
# registry with 62 dummy rows before registering itself, and IO.print
# adds one more, so the boot ends with all 64 rows written and the
# last row holding a live effect. The probe answers the registry
# length read from sys.c itself, and both real effects dispatch
# through the full table: a bound short of 64, or an off-by-one guard
# refusing the 64th registration, reddens this pin.
import Base

assert Reg.probe:
  IO(U32)

def Reg.probe():
  import "./io_eff_registry_bound.c"
  import "./io_eff_registry_bound.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    x : U32 <- Reg.probe()
    u : Unit <- IO.print(U32.show(x))
    return 0
$$ bend %
64
$$ bend % --seq
64
exit 0
$$ bend % --par
64
exit 0
$$ bend % --js
64
exit 0
