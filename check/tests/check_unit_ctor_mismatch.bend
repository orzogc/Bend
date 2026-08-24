# `()` is not a term: bend4 has no empty-tuple sugar, so the closing
# paren fails at the term position.
# ported from bend3: bend3 desugared () to U{}; bend4 pins the refusal
import Base

assert main:
  U32

def main(): ()
$$ bend %
Error:
- expected : a term
- observed : ')'
Location:
 8 | 
 9>| def main(): ()
10 |
