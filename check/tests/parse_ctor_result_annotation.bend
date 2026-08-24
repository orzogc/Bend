# audit 033: constructor result annotations are not part of parametric
# datatypes: a ctor row is Name{fields} and nothing follows it.
# ported from bend3
type Bad:
  Mk{} : U32

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
4 | type Bad:
5>|   Mk{} : U32
6 | 
