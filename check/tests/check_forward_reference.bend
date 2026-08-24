# term-level forward references FAIL as undefined: resolution follows
# book order.
# ported from bend3: bend3 ratified forward refs (C27); bend4 pins the
# refusal (the descent wall needs order)
import Base

assert main:
  U32

def main(): later

assert later:
  U32

def later(): 0
$$ bend %
Error:
- expected : a defined name
- observed : later
Location: main
 9 | 
10>| def main(): later
11 |
