# bend3 reserved the type name U32 at declarations; in bend4 U32 is a
# Base library name, not a keyword -- redeclaring it dies as an
# ordinary duplicate, which is the inverted law's own pin
import Base

assert U32:
  Type

def U32():
  Type
$$ bend %
Error:
- expected : a fresh name (duplicate declaration: U32)
- observed : ':'
Location:
5 | 
6>| assert U32:
7 |   Type
