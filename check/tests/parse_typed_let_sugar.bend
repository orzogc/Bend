# the typed-let statement is not grammar: a bend4 let is `x = v`, and a
# typed value spells the Ann brace, `x = {v : T}`.
# ported from bend3: bend3 ratified `x : T = v`; bend4 pins the refusal
import Base

assert main:
  U32

def main():
  z : U32 = 30
  z
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
 9 | def main():
10>|   z : U32 = 30
11 |   z
