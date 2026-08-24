# audit: the pre-freeze `Name : Data { .. }` datatype form is dead
# syntax -- the head fails as a top-level entry.
# ported from bend3
Nn7 : Data { Zz7{} }

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : 'N'
Location:
3 | # ported from bend3
4>| Nn7 : Data { Zz7{} }
5 | 
