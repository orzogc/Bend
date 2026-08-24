# audit: the unicode forall is dead syntax -- `@` is the forall binder.
# ported from bend3
import Base

assert t:
  Type

def t(): ∀x:U32.U32

assert main:
  U32

def main(): 0
$$ bend %
Error:
- expected : a term
- observed : '∀'
Location:
7 | 
8>| def t(): ∀x:U32.U32
9 |
