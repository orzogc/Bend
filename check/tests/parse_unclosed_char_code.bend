# bend3's unclosed backquote char-code scanned to end of input (the
# fixture lived in a second file); bend4 has no backquote word at all,
# so the tick dies in place and needs no fixture
import Base

assert main:
  U32

def main():
  `a
$$ bend %
Error:
- expected : a term
- observed : '`'
Location:
 9 | def main():
10>|   `a
11 |
