# io (io_flush_before_read): the kit flushes stdout before an effect
# that waits on the outside world, so a printed line is visible while
# the program blocks. "early" rides the stdio buffer (stdout is a
# pipe here), File.read's io_sync must flush it, and the companion
# then dies through _exit(7), which skips every stdio flush: "early"
# survives only if the read boundary already flushed it. Before this
# pin the buffer was dropped and stdout came out empty. The JS lanes
# own no C stdio and are not pinned here.
import Base

assert Exit.now:
  forall n: U32
  IO(Unit)

def Exit.now(n):
  import "./io_exit.c"
  import "./io_exit.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    u : Unit <- IO.print("early")
    f : File <- IO.try(File, File.open("/dev/null", "r"))
    m : File & Result<U32 & String, String> <- File.read(f, 4)
    x : Unit <- Exit.now(7)
    return 0
$$ bend % --seq
early
exit 7
$$ bend % --par
early
exit 7
