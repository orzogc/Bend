# a bare Char VALUE evaluates and prints as the quoted literal in the
# interpreter; the C host prints the raw character (SHOW_CHAR), the JS
# backend the quoted string.
# ported from bend3: unchanged program, per-lane spellings pinned
import Base

assert main.out:
  Char

def main.out():
  'x'

assert main:
  IO(Unit)

def main():
  IO.print(SCon{main.out(), SNil{}})
$$ bend %
x
$$ bend % --seq
x
exit 0
$$ bend % --par
x
exit 0
$$ bend % --js
x
exit 0
