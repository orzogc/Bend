# io (io_text_bytes): a String reaches the OS as BYTES, one byte per
# Char (code & 0xFF), in every lane -- the C kit's law (io_cstr, the
# Halt fputc walk) now binds the JS kit and both event loops. Before
# this pin, print.js, write.js, print_err.js and the two Halt lanes
# handed the raw JS string to process.std{out,err}.write, which UTF-8
# encodes: a program printing Chr{195}, Chr{169} wrote C3 A9 under C
# and C3 83 C2 A9 under --js and the interpreter -- the output
# divergence class SPEC 1.8 names a launch blocker (get_env held the
# read half: a 5-byte env value answered 5 chars in C, 4 in JS). The
# pinned text is the C lane's bytes, valid UTF-8 by construction, so
# every lane must produce them byte for byte on stdout AND stderr.
import Base

assert txt:
  String

def txt():
  SCon{Chr{101}, SCon{Chr{195}, SCon{Chr{169}, SNil{}}}}

assert acc:
  String

def acc():
  SCon{Chr{195}, SCon{Chr{169}, SNil{}}}

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    u : Unit <- IO.write(txt())
    v : Unit <- IO.print(acc())
    w : Unit <- IO.print_err(acc())
    IO.die(Unit, 7, acc())
$$ bend %
eéé
é
é
$$ bend % --seq
eéé
é
é
exit 7
$$ bend % --par
eéé
é
é
exit 7
$$ bend % --js
eéé
é
é
exit 7
