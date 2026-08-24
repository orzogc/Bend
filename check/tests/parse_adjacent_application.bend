# application never binds through a space: App's `(` is GLUED to its
# head, so `id (0)` is not a call.
# ported from bend3: bend3 ratified space-application; bend4 pins the
# opposite (glued) law, so the port is the refusal
import Base

assert id:
  forall x: U32
  U32

def id(x): x

assert main:
  U32

def main(): id (0)
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : '('
Location:
15 | 
16>| def main(): id (0)
17 |
