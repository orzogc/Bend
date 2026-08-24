# bend3's >2^16-slot slab representation and its past-capacity no-op
# laws; bend4's Array is a materialized tree with no slab tier -- the
# big sparse literal's spelling is the refusal
import Base

assert main:
  U32

def main():
  m : [:U32] = ![70000:1, _:0; 131072]
  m[70000]
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
 9 | def main():
10>|   m : [:U32] = ![70000:1, _:0; 131072]
11 |   m[70000]
