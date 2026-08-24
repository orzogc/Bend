# io (io_fail_flush): a fail-stop abort keeps the stdout the program
# already printed. "kept" rides the stdio buffer (the test captures
# stdout through a pipe, so it is fully buffered), then Short.arm(0)
# makes IO.print's next fwrite answer short and io_out fail-stops:
# "kept" must still come out. Apple Libc's abort flushes open streams
# before raising SIGABRT, so err_fail spends no explicit flush; this
# pin guards that contract against a platform shift or an err_fail
# respelled over a raw exit. The JS lanes own no C stdio and are not
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
    u : Unit <- IO.print("kept")
    v : Unit <- Short.arm(0)
    w : Unit <- IO.print("never")
    return 0
$$ bend % --seq
kept
bend: error 1: a short write on a standard stream
signal SIGABRT
$$ bend % --par
kept
bend: error 1: a short write on a standard stream
signal SIGABRT
