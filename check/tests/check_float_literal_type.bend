# a float literal is an F32: at a U32 goal the build's F32 result is
# refused (bend3 pinned its literal typing; the desugared spelling
# shows in the observed type)
import Base

assert main:
  U32

def main():
  1.5
$$ bend %
Error:
- expected : U32
- observed : F32
Location: main
 9 | def main():
10>|   1.5
11 |
