# refusal pin: bend3 rejected a non-Data argument at a Data-bounded
# datatype param inside another datatype's ctor field (dat_check
# formation). bend4 has no Data kind to bound a param with, so the
# faithful translation dies one wall earlier: Data is not a defined
# name, refused at Box7's own head.
import Base

type Box7<T: Data>:
  MkBox7{v: T}
type Bad:
  MkBad{v: Box7<U32 -> U32>}

assert main:
  U32

def main(): 0
$$ bend %
Error:
- expected : a defined name
- observed : Data
Location:
7 | 
8>| type Box7<T: Data>:
9 |   MkBox7{v: T}
