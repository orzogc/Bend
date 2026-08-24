# io (io_codec_oom_malloc): a failed codec allocation refuses loud,
# never through NULL. The companion interposes the binary's own malloc
# and realloc over the default malloc zone, and Oom.arm(0) makes the
# next allocation call answer NULL: here that call is io_cstr's malloc
# inside IO.print. The kit must fail-stop with the plain numbered host
# out-of-memory error. Before this pin io_cstr wrote through the NULL
# buffer and both C lanes died "error 10: memory fault" - a wrong-class
# crash, not a refusal - while the interpreter and --js printed "never"
# and exited 0. The JS lanes own no allocator and are not pinned here.
import Base

assert Oom.arm:
  forall n: U32
  IO(Unit)

def Oom.arm(n):
  import "./io_codec_oom.c"
  import "./io_codec_oom.js"

assert main:
  IO(U32)

def main():
  do IO<U32>:
    u : Unit <- Oom.arm(0)
    v : Unit <- IO.print("never")
    return 0
$$ bend % --seq
bend: error 5: host allocation failed
signal SIGABRT
$$ bend % --par
bend: error 5: host allocation failed
signal SIGABRT
