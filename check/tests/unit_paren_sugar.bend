# bend3's () sugar for the Unit constructor, value and pattern; bend4
# has no unit literal -- the pattern spelling dies at parse
import Base

assert tick:
  forall u: Unit
  U32

def tick(u):
  match u:
    case ():
      7

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a term
- observed : ')'
Location:
10 |   match u:
11>|     case ():
12 |       7
