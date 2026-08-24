# refusal pin: bend3's sort fixpoint grew P's table through its own
# declaration and refused a t: Type bound at the Box formation inside
# it. bend4 has no Data kind at all, so the faithful translation dies
# one wall earlier: Data is not a defined name, refused at Box5's own
# head before P6's self-reference is ever weighed.
import Base

type Box5<T: Data>:
  MkBox5{v: T}
type P6<T: Type>:
  MkP6{v: Box5<P6<T>>}
  End6{w: T}

assert main:
  U32

def main(): 0
$$ bend %
Error:
- expected : a defined name
- observed : Data
Location:
7 | 
8>| type Box5<T: Data>:
9 |   MkBox5{v: T}
