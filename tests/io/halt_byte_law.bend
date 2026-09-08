# io (io_halt_byte_law): the loop's exit writer rides the kit's byte
# law -- Halt prints its message on stderr as BYTES, one per Char, on
# every lane. io_print_byte_law pins the kit writers and io_halt_exits
# pins the halt path only through ASCII, yet the halt writer is three
# separate spellings (the C loop's fputc cast, the JS runtime's and
# the interpreter's & 255 loops), so a re-encoding drift in any one of
# them was invisible. Chars 195,168 are the UTF-8 byte spelling of
# "e-grave": a lane that re-encodes the code point prints four bytes
# where the law prints two. A code point past 255 falls outside the
# law and truncates to its low byte identically on every lane
# (10049 & 255 = 65, "A"), the C cast's own behavior.
import Base

law main:
  IO(Unit)

def main():
  IO.die(Unit, 7, SCon{Chr{195}, SCon{Chr{168}, SCon{Chr{10049}, SNil{}}}})

#|èA
#|exit 7
