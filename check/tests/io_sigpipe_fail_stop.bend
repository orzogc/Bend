# io (io_sigpipe_fail_stop): the C kit ignores SIGPIPE (io_sys_boot),
# so a write into a pipe whose reader is gone surfaces as EPIPE and
# rides the fail-stop write law -- one loud numbered line, never a
# silent death by signal. The companion replaces fd 1 with the write
# end of a pipe whose read end it closed: the print lands in stdio's
# full buffer and the exit flush (io_sync) meets EPIPE. Without the
# ignore, the flush dies by SIGPIPE first -- exit 141 and an EMPTY
# stderr, proven by gutting the signal line -- so the stated law rode
# on nothing: a kit rewrite dropping io_sys_boot kept the whole suite
# green while every piped-consumer death went silent. The JS kit
# meets the same EPIPE at its checked writeSync (bun ignores SIGPIPE
# itself); the interp lane stays unpinned as in io_stdout_fail_stop
# (in-process, fd 1 is the harness's own stdout). The socket half --
# a send into a reset peer answers Fail, never a signal death -- is
# not deterministically drivable (the reset races the send), so the
# csrc pins hold both guards where they live.
# csrc has: signal(SIGPIPE, SIG_IGN)
# csrc has: SO_NOSIGPIPE
import Base

assert Pipe.probe:
  IO(U32)

def Pipe.probe():
  import "./io_sigpipe_fail_stop.c"
  import "./io_sigpipe_fail_stop.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    x : U32 <- Pipe.probe()
    u : Unit <- IO.print("the dropped line")
    return x
$$ bend % --seq
bend: error 1: a short write on a standard stream
signal SIGABRT
$$ bend % --par
bend: error 1: a short write on a standard stream
signal SIGABRT
$$ bend % --js
bend: error 1: a short write on a standard stream
exit 1
