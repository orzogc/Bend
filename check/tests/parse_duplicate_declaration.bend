# audit 010: duplicate top-level declarations are rejected.
# ported from bend3
type Uu:
  Un{}

assert main:
  Uu

def main(): Un{}
assert main:
  Uu

def main(): Un{}
$$ bend %
Error:
- expected : a fresh name (duplicate declaration: main)
- observed : ':'
Location:
 9 | def main(): Un{}
10>| assert main:
11 |   Uu
