# over-application: the page states the head's actual type
import Base
assert id:
  U32 -> U32

def id(): x => x
assert main:
  U32

def main(): id(1, 2)

$$ bend %
Error:
- expected : a function type
- observed : U32
Location: main
 9 | 
10>| def main(): id(1, 2)
11 |
