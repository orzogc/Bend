# audit: the unicode lambda is dead syntax -- `=>` is the lambda form.
# ported from bend3
import Base

assert id:
  @_:U32 -> U32

def id(): λx.x

assert main:
  U32

def main(): id(7)
$$ bend %
Error:
- expected : a term
- observed : 'λ'
Location:
7 | 
8>| def id(): λx.x
9 |
