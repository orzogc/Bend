# io (io_out_short_write): a short write on a standard stream refuses
# loud, never silently succeeds. The companion interposes the binary's
# own fwrite behind an armed countdown (unarmed calls forward byte by
# byte through libc fputc, so stdio buffering stays real), and
# Short.arm(0) makes the next fwrite answer 0: here that call is
# io_out's inside IO.print. Before this pin the kit ignored the fwrite
# result, so a failed stdout write printed nothing and both C lanes
# exited 0 claiming success. The JS lanes own no C stdio and are not
# pinned here.
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
    u : Unit <- Short.arm(0)
    v : Unit <- IO.print("never")
    return 0
$$ bend % --seq
bend: error 1: a short write on a standard stream
signal SIGABRT
$$ bend % --par
bend: error 1: a short write on a standard stream
signal SIGABRT
