# bend3's -o grouping lane re-minted let keys and this fuzz shape
# caught a scope leak; bend4 has no grouping lane and no % modulo at
# all (% heads a rewrite), so the shape's arithmetic core dies at
# parse on its own operator
import Base

assert pa3:
  forall a: U32
  forall b: U32
  forall c: U32
  U32

def pa3(a, b, c):
  ((a + b) - c) - (65536 % 2147483648)

assert main:
  U32

def main():
  pa3(4, 7, 1)
$$ bend %
Error:
- expected : ')'
- observed : '%'
Location:
13 | def pa3(a, b, c):
14>|   ((a + b) - c) - (65536 % 2147483648)
15 |
