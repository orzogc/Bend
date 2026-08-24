# slab-array pin (check_array_default_distinct): bend3 held array
# literals with equal entries but DIFFERENT defaults non-convertible
# (reads past the keys distinguish them). bend4 has no array literals
# -- the ![ spelling inside the equality goal pins bend4's own parse
# refusal.
import Base

assert bad:
  {![0:1, _:7; 1] == ![0:1, _:8; 1] : [:U32]}

def bad():
  {==}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a term
- observed : '!'
Location:
 8 | assert bad:
 9>|   {![0:1, _:7; 1] == ![0:1, _:8; 1] : [:U32]}
10 |
