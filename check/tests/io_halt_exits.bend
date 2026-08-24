# io (io_halt_exits): the loop's answer ENDS the program. SPEC 1.8:
# Halt prints its message on stderr as bytes and exits its code, and
# the C loop returns that code straight through main, so nothing can
# run after it. The JS lanes instead queued the stderr write on the
# process stream and set process.exitCode, drifting to a natural
# exit: host work an effect left behind - the companion parks a
# zero-delay timer that prints - still ran AFTER the program halted,
# and the halt message rode a queued stream where the kit's own law
# writes fd 1/2 sync. Before this pin the --js lane printed the
# timer's line; now the driver exits at io_run's answer, the halt
# bytes go out via one sync write, and the timer dies unfired,
# matching the C lanes byte for byte. The interp lane stays
# unpinned: the suite runs it in-process, where the parked timer
# would fire into the harness itself; the CLI proves it by hand.
import Base

assert Halt.probe:
  IO(Unit)

def Halt.probe():
  import "./io_halt_exits.c"
  import "./io_halt_exits.js"

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    u : Unit <- Halt.probe()
    IO.die(Unit, 7, "boom")
$$ bend % --seq
boom
exit 7
$$ bend % --par
boom
exit 7
$$ bend % --js
boom
exit 7
