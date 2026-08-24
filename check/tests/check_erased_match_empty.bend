# audit: empty elimination cannot inspect an erased argument.
# ported from bend3
type Empty9:

type Unit9:
  Uu9{}

assert bad:
  @-e:Empty9 -> Empty9

def bad(): \{}

assert main:
  Unit9

def main(): Uu9{}
$$ bend %
Error:
- message  : a live scrutinee (a - scrutinee matches only in a dead region)
Location: bad
10 | 
11>| def bad(): \{}
12 |
