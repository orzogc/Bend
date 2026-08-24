# io (io_flush_before_stderr): a stderr write is a stream seam, so
# the C kit flushes stdout before it - without the flush, stdout
# rides the stdio buffer (a pipe here) while stderr is unbuffered,
# and a merged stream (2>&1) shows the stderr bytes BEFORE stdout
# lines the program printed FIRST, while the JS lanes write both
# descriptors synchronously and keep program order: an output-order
# divergence between the backends (SPEC 1.8). "early" rides the
# buffer, IO.print_err's io_errs must flush it, and the companion
# then dies through _exit(7), which skips every stdio flush: "early"
# survives only if the stderr seam already flushed it. The --js
# lane pins the agreeing content: its writes land in program order
# (the interpreter runs in-process, where Exit.now would take the
# harness worker with it, so that block is not pinned here).
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
    v : Unit <- IO.print_err("seam")
    x : Unit <- Exit.now(7)
    return 0
$$ bend % --seq
early
seam
exit 7
$$ bend % --par
early
seam
exit 7
$$ bend % --js
early
seam
exit 7
