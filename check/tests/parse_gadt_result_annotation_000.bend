# audit: native datatypes are parametric, not indexed by constructor
# targets -- a ctor row takes no result annotation.
# ported from bend3: parens params become angles
type Ix<n: Nat>:
  I0{} : Ix(0n)

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
4 | type Ix<n: Nat>:
5>|   I0{} : Ix(0n)
6 | 
