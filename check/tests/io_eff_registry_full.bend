# io (io_eff_registry_full): the 65th effect registration refuses
# loud. The companion pads the registry with 63 dummy rows before
# registering itself, and IO.print makes the 65th: past IO_EFFS = 64
# the boot must fail-stop with a plain numbered error. Before this
# pin io_eff wrote the overflow row into the statics beside the
# registry arrays (a global-buffer-overflow under ASan), so the
# corrupted table could no longer dispatch the program's own request
# and both C lanes died "an alien request" - a corruption, not a
# refusal. The JS lanes own no registry and are not pinned here.
import Base

assert Reg.probe:
  IO(U32)

def Reg.probe():
  import "./io_eff_registry_full.c"
  import "./io_eff_registry_full.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    x : U32 <- Reg.probe()
    u : Unit <- IO.print(U32.show(x))
    return 0
$$ bend % --seq
bend: error 6: the effect registry is full
signal SIGABRT
$$ bend % --par
bend: error 6: the effect registry is full
signal SIGABRT
