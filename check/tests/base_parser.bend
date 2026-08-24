# bend3's Parser combinator module is absent from bend4's base (number
# text rides U32.read/Nat.read): the head call is an undefined name
import Base

assert main:
  U32

def main():
  Parser.digits()
$$ bend %
Error:
- expected : a defined name
- observed : Parser.digits
Location: main
 8 | def main():
 9>|   Parser.digits()
10 |
