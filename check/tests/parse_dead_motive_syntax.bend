# bend3's dead %[x => P] motive spelling died as list syntax; bend4's
# rewrite is `%e : P` and [ after % has no reading at all -- the old
# spelling dies at parse
import Base

assert sym3:
  forall -x: U32
  forall -y: U32
  forall e: {x == y : U32}
  {y == x : U32}

def sym3(x, y, e):
  %[h => {y == h : U32}] e {=}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : ':'
- observed : 'e'
Location:
12 | def sym3(x, y, e):
13>|   %[h => {y == h : U32}] e {=}
14 |
