# ^ is no operator (bitwise xor is dotted, .^.): after a full term the
# parser closes the def and a bare caret is refused at the top level
import Base

assert main:
  U32

def main():
  1 ^ 2
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : '^'
Location:
 8 | def main():
 9>|   1 ^ 2
10 |
