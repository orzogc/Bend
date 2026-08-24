# string literals are core grammar, ungated: ".." builds SCon/SNil
# with Base's String in scope (bend3 gated the sugar on `import
# String`)
import Base

assert main.out:
  String

def main.out():
  "hi" ++ "!"

assert main:
  IO(Unit)

def main():
  IO.print(main.out())
$$ bend %
hi!
$$ bend % --seq
hi!
exit 0
$$ bend % --par
hi!
exit 0
$$ bend % --js
hi!
exit 0
