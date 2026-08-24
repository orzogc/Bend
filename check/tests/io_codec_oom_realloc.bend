# io (io_codec_oom_realloc): a failed codec regrow refuses loud, never
# through NULL. io_cstr starts at a 64-byte buffer and doubles it at
# the 63rd character, so printing this 80-character string reallocs
# exactly once: Oom.arm(1) lets the malloc pass and makes the realloc
# answer NULL. The kit must fail-stop with the plain numbered host
# out-of-memory error. Before this pin io_cstr assigned the NULL
# straight over the buffer (leaking it) and wrote through it, so both
# C lanes died "error 10: memory fault" - a wrong-class crash, not a
# refusal - while the interpreter and --js printed the string and
# exited 0. The JS lanes own no allocator and are not pinned here.
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
    u : Unit <- Oom.arm(1)
    v : Unit <- IO.print("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
    return 0
$$ bend % --seq
bend: error 5: host allocation failed
signal SIGABRT
$$ bend % --par
bend: error 5: host allocation failed
signal SIGABRT
