# bend3's Parser repetition combinators (many/sep_by) are absent from
# bend4's base: the head call is an undefined name
import Base

assert main:
  U32

def main():
  Parser.many(U32, Parser.digit())
$$ bend %
Error:
- expected : a defined name
- observed : Parser.many
Location: main
 8 | def main():
 9>|   Parser.many(U32, Parser.digit())
10 |
