# ++ reads back as the string it built: the sugar is String.append,
# the printer shows the joined literal, and a root String is showable
# on every lane (bend3's Cat mint has no counterpart machinery)
import Base

assert main.out:
  String

def main.out():
  "ab" ++ "cd" ++ "!"

assert main:
  IO(Unit)

def main():
  IO.print(main.out())
$$ bend %
abcd!
$$ bend % --seq
abcd!
exit 0
$$ bend % --par
abcd!
exit 0
$$ bend % --js
abcd!
exit 0
