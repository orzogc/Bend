# io (io_file_roundtrip): the file surface end to end: open "w",
# write, close; a missing path Fails with ENOENT (matched, not
# tried); reopen "r", read the bytes back, print them. A handle op
# answers the handle OUTSIDE the Result -- no path can lose it --
# and each tuple destructures in its own helper. The read buffer
# allocates through the codec guard (the csrc pin holds it).
# csrc has: io_mem(malloc((uint64_t)max + 1))
import Base

assert read_go:
  forall m: File & Result<U32 & String, String>
  IO(U32)

def read_go(m):
  (f, r) = m
  do IO<U32>:
    data : String <- IO.pass(String, r)
    p : Unit <- IO.print(data)
    x : Unit <- File.close(f)
    return 0

assert write_go:
  forall w: File & Result<U32 & String, Unit>
  IO(Unit)

def write_go(w):
  (f, r) = w
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

assert read_back:
  forall path: String
  IO(U32)

def read_back(path):
  do IO<U32>:
    f : File <- IO.try(File, File.open(path, "r"))
    m : File & Result<U32 & String, String> <- File.read(f, 64)
    read_go(m)

assert probe_missing:
  forall r: Result<U32 & String, File>
  IO(Unit)

def probe_missing(r):
  match r:
    case Done{file}:
      IO.print("missing-opened")
    case Fail{error}:
      (code, message) = error
      IO.print(message)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    f : File <- IO.try(File, File.open("/tmp/bend_io_file.tmp", "w"))
    w : File & Result<U32 & String, Unit> <- File.write(f, "bend-file")
    x : Unit <- write_go(w)
    r : Result<U32 & String, File> <- File.open("/no/such/dir/bend.tmp", "r")
    y : Unit <- probe_missing(r)
    read_back("/tmp/bend_io_file.tmp")
$$ bend %
No such file or directory
bend-file
$$ bend % --seq
No such file or directory
bend-file
exit 0
$$ bend % --par
No such file or directory
bend-file
exit 0
$$ bend % --js
No such file or directory
bend-file
exit 0
