# io (io_path_byte_law): the PATH byte law's past-255 truncation,
# beside io_path_bytes' in-range and raw-byte pins: a path Char
# whose code exceeds 255 reaches the OS as its LOW BYTE, so a file
# written through Chr{321} reads back through "A" (321 & 255 = 65:
# one file, not two) identically in every lane. A re-encoding lane
# writes the two UTF-8 bytes C5 81 instead and prints "missing".
import Base

assert write_go:
  forall w: File & Result<U32 & String, Unit>
  IO(Unit)

def write_go(w):
  (f, r) = w
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

assert read_go:
  forall m: File & Result<U32 & String, String>
  IO(Unit)

def read_go(m):
  (f, r) = m
  do IO<Unit>:
    data : String <- IO.pass(String, r)
    p : Unit <- IO.print("found " ++ data)
    File.close(f)

assert read_probe:
  forall r: Result<U32 & String, File>
  IO(Unit)

def read_probe(r):
  match r:
    case Done{file}:
      do IO<Unit>:
        m : File & Result<U32 & String, String> <- File.read(file, 64)
        read_go(m)
    case Fail{error}:
      (code, message) = error
      IO.print("missing")

assert main:
  IO(U32)

def main():
  do IO<U32>:
    f : File <- IO.try(File, File.open("/tmp/bend_io_path_law_" ++ SCon{Chr{321}, SNil{}}, "w"))
    w : File & Result<U32 & String, Unit> <- File.write(f, "law")
    x : Unit <- write_go(w)
    r : Result<U32 & String, File> <- File.open("/tmp/bend_io_path_law_A", "r")
    a : Unit <- read_probe(r)
    return 0
$$ bend %
found law
$$ bend % --seq
found law
exit 0
$$ bend % --par
found law
exit 0
$$ bend % --js
found law
exit 0
