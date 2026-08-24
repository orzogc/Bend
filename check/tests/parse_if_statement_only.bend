# bend3 confined if to statement position; bend4's if is a TERM, legal
# in any argument or operand slot. a literal condition rides an
# ascription: the applied match's scrutinee must infer
import Base

assert main.out:
  U32

def main.out():
  1 + (if {False{} : Bool}: 10 else: 20) + (if {True{} : Bool}: 300 else: 400)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
321
$$ bend % --seq
321
exit 0
$$ bend % --js
321
exit 0
