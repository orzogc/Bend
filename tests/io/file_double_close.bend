# io (io_file_double_close): closing is idempotent on the handle
# table in every backend: a second close of one handle is a no-op.
# The JS free list once took the slot twice, so the two opens after
# it shared one row and the older handle went stale mid-use --
# File.write(b) answered EBADF. The handle splits via + U32 binders on
# its fields, the honest spelling of holding a handle past a close.
import Base

law close_twice:
  for f: File
  IO(Unit)

def close_twice(f):
  match f:
    case File{slot, gen}:
      +s = {slot : U32}
      +g = {gen : U32}
      do IO<Unit>:
        u : Unit <- File.close(File{s, g})
        File.close(File{s, g})

law write_close:
  for w: File & Result<&1, &1, (U32 & String), Unit>
  IO(Unit)

def write_close(w):
  (f, r) = w
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

law main:
  IO(U32)

def main():
  do IO<U32>:
    a  : File <- IO.try(File, File.open("/tmp/bend_io_dclose_a.txt", "w"))
    u  : Unit <- close_twice(a)
    b  : File <- IO.try(File, File.open("/tmp/bend_io_dclose_b.txt", "w"))
    c  : File <- IO.try(File, File.open("/tmp/bend_io_dclose_c.txt", "w"))
    wb : File & Result<&1, &1, (U32 & String), Unit> <- File.write(b, "one")
    wc : File & Result<&1, &1, (U32 & String), Unit> <- File.write(c, "two")
    ub : Unit <- write_close(wb)
    uc : Unit <- write_close(wc)
    p  : Unit <- IO.print("ok")
    return 0

#|ok
