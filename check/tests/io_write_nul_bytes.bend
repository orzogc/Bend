# io (io_write_nul_bytes): bytes ride Strings as code points 0..255
# and NUL is a byte like any other: the payload "a\0b" writes whole
# and reads back equal in every backend. A backend that hands the
# bytes to a C-string API truncates at the NUL and breaks this pin
# -- the C kit once printed through fputs; it writes by length now.
import Base

assert payload:
  String

def payload():
  SCon{'a', SCon{Chr{0}, SCon{'b', SNil{}}}}

assert verdict:
  forall back: String
  IO(Unit)

def verdict(back):
  if String.eq(back, payload()):
    IO.print("whole")
  else:
    IO.print("cut")

assert write_go:
  forall w: File & Result<U32 & String, Unit>
  IO(File)

def write_go(w):
  (f, r) = w
  do IO<File>:
    u : Unit <- IO.pass(Unit, r)
    return f

assert read_go:
  forall m: File & Result<U32 & String, String>
  IO(U32)

def read_go(m):
  (f, r) = m
  do IO<U32>:
    back : String <- IO.pass(String, r)
    v : Unit <- verdict(back)
    x : Unit <- File.close(f)
    return 0

assert main:
  IO(U32)

def main():
  do IO<U32>:
    f : File <- IO.try(File, File.open("/tmp/bend_io_nul.tmp", "w"))
    w : File & Result<U32 & String, Unit> <- File.write(f, payload())
    f2 : File <- write_go(w)
    x : Unit <- File.close(f2)
    g : File <- IO.try(File, File.open("/tmp/bend_io_nul.tmp", "r"))
    m : File & Result<U32 & String, String> <- File.read(g, 8)
    read_go(m)
$$ bend %
whole
$$ bend % --seq
whole
exit 0
$$ bend % --par
whole
exit 0
$$ bend % --js
whole
exit 0
