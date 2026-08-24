# bend3's buffer literal rejected duplicate keys; bend4 has no buffer
# literal -- [..] is the list literal, where a key's ':' has no
# reading and the spelling dies at parse
import Base

assert main:
  List<U32>

def main():
  [0:1,0:2,_:0;2]
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
 9 | def main():
10>|   [0:1,0:2,_:0;2]
11 |
