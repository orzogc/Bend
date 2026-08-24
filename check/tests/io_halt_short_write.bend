# io (io_halt_short_write): Halt's message rides the same checked
# stderr seam as IO.print_err (io_errs: flush stdout, then io_out),
# so a short stderr write at the halt boundary fail-stops loud - the
# old raw fputc drain ignored short writes and skipped the flush.
# Short.arm(0) makes the next write answer short: with Halt routed
# through io_errs, its message write fail-stops before a byte of
# "gone" lands; a drain respelled over unchecked fputc would print
# "gone" and exit 7 instead. The --js lane joins the law: io_run's
# Halt arm fail-stops through the kit's io_out spelling (one error
# line, exit 1), where a swallowing catch would exit 7 with the
# failed write hidden - the C/JS split this golden guards. The
# interpreter shares io_run and runs in the harness worker, so its
# block is not pinned here.
# csrc has: io_errs(e, fs[1]);
import Base

assert Short.arm:
  forall n: U32
  IO(Unit)

def Short.arm(n):
  import "./io_short.c"
  import "./io_short.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    v : Unit <- Short.arm(0)
    x : Unit <- IO.die(Unit, 7, "gone")
    return 0
$$ bend % --seq
bend: error 1: a short write on a standard stream
signal SIGABRT
$$ bend % --par
bend: error 1: a short write on a standard stream
signal SIGABRT
$$ bend % --js
bend: error 1: a short write on a standard stream
exit 1
