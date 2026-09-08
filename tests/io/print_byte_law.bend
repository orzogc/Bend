# io (io_print_byte_law): the kit's byte law on the writers -- bytes
# ride Strings as code points 0..255, so print, write and print_err
# emit each Char as ONE raw byte on every lane, never a UTF-8
# re-encoding of the code point. Chars 195,168 are the UTF-8 byte
# spelling of "e-grave": a lane that re-encodes prints four bytes
# ("A-tilde, diaeresis") where the law prints two. A code point past
# 255 falls outside the law and truncates to its low byte identically
# on every lane (10049 & 255 = 65, "A"), the C cast's own behavior.
import Base

law main:
  IO(Unit)

def main():
  do IO<Unit>:
    a : Unit <- IO.write(SCon{Chr{195}, SCon{Chr{168}, SNil{}}})
    b : Unit <- IO.print(SCon{Chr{10049}, SNil{}})
    c : Unit <- IO.print_err(SCon{Chr{195}, SCon{Chr{169}, SNil{}}})
    return Unit{}

#|èA
#|é
