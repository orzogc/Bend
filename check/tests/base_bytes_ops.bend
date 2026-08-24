# bend3's Bytes module (encode/pack/to_list) has no bend4 surface: a
# Bytes value is an Array of U32 by ruling, and no Bytes namespace
# exists in base -- the head call is an undefined name
import Base

assert main:
  U32

def main():
  Bytes.encode("banana")
$$ bend %
Error:
- expected : a defined name
- observed : Bytes.encode
Location: main
 9 | def main():
10>|   Bytes.encode("banana")
11 |
