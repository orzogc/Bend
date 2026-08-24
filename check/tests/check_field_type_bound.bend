# audit: datatype field types are checked before definitions use them.
# ported from bend3
type Bad9:
  Mk9{x: Missing9}

assert main:
  Bad9

def main(): Mk9{}
$$ bend %
Error:
- expected : a defined name
- observed : Missing9
Location:
3 | type Bad9:
4>|   Mk9{x: Missing9}
5 | 
