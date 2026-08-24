# io (io_file_double_close): closing is idempotent on the handle
# table in every backend: a second close of one handle is a no-op.
# The JS free list once took the slot twice, so the two opens after
# it shared one row and the older handle went stale mid-use --
# File.write(b) answered EBADF. The handle splits via U32.copy on
# its fields, the honest spelling of holding a handle past a close.
import Base

assert close_twice:
  forall f: File
  IO(Unit)

def close_twice(f):
  match f:
    case File{slot, gen}:
      +s = {slot : +U32}
      +g = {gen : +U32}
      do IO<Unit>:
        u : Unit <- File.close(File{s, g})
        File.close(File{s, g})

assert write_close:
  forall w: File & Result<U32 & String, Unit>
  IO(Unit)

def write_close(w):
  (f, r) = w
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : File <- IO.try(File, File.open("/tmp/bend_io_dclose_a.txt", "w"))
    u : Unit <- close_twice(a)
    b : File <- IO.try(File, File.open("/tmp/bend_io_dclose_b.txt", "w"))
    c : File <- IO.try(File, File.open("/tmp/bend_io_dclose_c.txt", "w"))
    wb : File & Result<U32 & String, Unit> <- File.write(b, "one")
    wc : File & Result<U32 & String, Unit> <- File.write(c, "two")
    ub : Unit <- write_close(wb)
    uc : Unit <- write_close(wc)
    p : Unit <- IO.print("ok")
    return 0
$$ bend %
ok
$$ bend % --seq
ok
exit 0
$$ bend % --par
ok
exit 0
$$ bend % --js
ok
exit 0
