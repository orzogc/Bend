# a float literal is digits '.' digits: a trailing name char after the
# dot is not a float, and the numeric parser refuses it whole
import Base

assert main:
  U32

def main():
  1.x
$$ bend %
Error:
- expected : a numeric literal (NUMBER is U32, NUMBER n is Nat)
- observed : '.'
Location:
 8 | def main():
 9>|   1.x
10 |
