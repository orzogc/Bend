# io (io_codec_seal_shared): a string built ON THE SEAM and handed to
# a program that refcounts String must arrive SEALED. This book keeps
# a String binder (+s over the Str.copy witness), so SCon is hot and
# the book's IO_HOTS mask carries bit 1: the u32_show native (the
# digit leg shares U32.show's answer) and the kit's io_str codec (the
# file leg shares File.read's answer) both rfc_seal the tail they
# store. Unsealed, a shared take meets a raw non-trivial field and
# span_fade posts error 9. The Tuple, Done and Fail bits ride on no
# drivable program (base ships no Copiable witness for them), so the
# csrc pins hold their seal sites, and the mask itself, verbatim.
# csrc has: #define IO_HOTS 1
# csrc has: IO_HOTS & 1 ? rfc_seal(e, s) : s
# csrc has: io_seal(e, s, IO_HOTS & 1)
# csrc has: io_seal(e, a, IO_HOTS & 2)
# csrc has: io_seal(e, b, IO_HOTS & 2)
# csrc has: io_seal(e, v, IO_HOTS & 4)
# csrc has: io_seal(e, t, IO_HOTS & 8)
import Base

assert Chr.copy:
  forall c: Char
  Copy(Char, c) & Copy(Char, c)

def Chr.copy(c):
  match c:
    case Chr{n}:
      ((nx, ne), (ny, nf)) = U32.copy(n)
      e1 = Equal.cong(U32, Char, z => Chr{z}, n, nx, ne)
      e2 = Equal.cong(U32, Char, z => Chr{z}, n, ny, nf)
      ((Chr{nx}, e1), (Chr{ny}, e2))

assert Str.copy:
  forall s: String
  Copy(String, s) & Copy(String, s)

def Str.copy(s):
  match s:
    case SNil{}:
      ((SNil{}, {==}), (SNil{}, {==}))
    case SCon{h, t}:
      ((hx, he), (hy, hf)) = Chr.copy(h)
      ((tx, te), (ty, tf)) = Str.copy(t)
      s10 = Equal.cong(Char, String, z => SCon{z, t}, h, hx, he)
      s11 = Equal.cong(String, String, z => SCon{hx, z}, t, tx, te)
      t11 = Equal.trans(String, SCon{h, t}, SCon{hx, t}, SCon{hx, tx}, s10, s11)
      s20 = Equal.cong(Char, String, z => SCon{z, t}, h, hy, hf)
      s21 = Equal.cong(String, String, z => SCon{hy, z}, t, ty, tf)
      t21 = Equal.trans(String, SCon{h, t}, SCon{hy, t}, SCon{hy, ty}, s20, s21)
      ((SCon{hx, tx}, t11), (SCon{hy, ty}, t21))

assert twice:
  forall +s: (+ String ~ Str.copy)
  String

def twice(s):
  String.append(s, s)

assert read_go:
  forall m: File & Result<U32 & String, String>
  IO(U32)

def read_go(m):
  (f, r) = m
  do IO<U32>:
    data : String <- IO.pass(String, r)
    p : Unit <- IO.print(twice(data))
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

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : Unit <- IO.print(twice(U32.show(41)))
    f : File <- IO.try(File, File.open("/tmp/bend_io_hots.tmp", "w"))
    w : File & Result<U32 & String, Unit> <- File.write(f, "abc")
    x : Unit <- write_go(w)
    g : File <- IO.try(File, File.open("/tmp/bend_io_hots.tmp", "r"))
    m : File & Result<U32 & String, String> <- File.read(g, 64)
    read_go(m)
$$ bend %
4141
abcabc
$$ bend % --seq
4141
abcabc
exit 0
$$ bend % --par
4141
abcabc
exit 0
$$ bend % --js
4141
abcabc
exit 0
