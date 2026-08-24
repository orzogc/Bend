# io (io_print_write): print (newline) and write (raw) sequence in
# order through the event loop, and U32.show feeds a computed string
# to an effect. Ported from bend3; bend3's result-word exit code was
# bend3 CLI behavior -- bend4's loop discards the Emit word, and the
# interp lane pins no exit line.
import Base

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : Unit <- IO.print("hello")
    b : Unit <- IO.write("num=")
    c : Unit <- IO.print(U32.show(40 + 2))
    return 7
$$ bend %
hello
num=42
$$ bend % --seq
hello
num=42
exit 0
$$ bend % --par
hello
num=42
exit 0
$$ bend % --js
hello
num=42
exit 0
