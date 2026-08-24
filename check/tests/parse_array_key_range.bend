# bend3's slab-array literal [k:v; n] is gone: [..] is the list
# literal, whose elements are terms -- a key:value entry is refused by
# the grammar itself
import Base

assert main:
  U32

def main():
  m = [0:5, _:0; 1]
  0
$$ bend %
Error:
- expected : a term
- observed : ':'
Location:
 9 | def main():
10>|   m = [0:5, _:0; 1]
11 |   0
