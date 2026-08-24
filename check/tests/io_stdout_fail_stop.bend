# io (io_stdout_fail_stop): a lost stdout write is loud, never a
# silent success. Stdio buffers a piped stdout in full, so a failed
# write surfaces only when the buffer flushes - and the flush the C
# exit path runs discards its error, so a program whose output never
# landed still answered exit 0. The companion closes stdout before
# the print: the print lands in the buffer, and the loop's exit
# boundary (io_sync in main) must refuse the unflushable stream.
# Before this pin both C lanes printed nothing and exited 0. The JS
# kit owns no stdio buffer, so its writeSync fails at the print
# itself (the companion closes fd 1 through libc; bun shields its
# own closeSync) - and before this pin the kit swallowed the error,
# so the js lane too printed nothing and exited 0. The interp lane
# stays unpinned: the suite runs it in-process, where closing fd 1
# would take the harness's own stdout down.
import Base

assert Out.probe:
  IO(U32)

def Out.probe():
  import "./io_stdout_fail_stop.c"
  import "./io_stdout_fail_stop.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    x : U32 <- Out.probe()
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
