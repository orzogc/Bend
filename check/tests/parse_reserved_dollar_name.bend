# audit 007: '$' is not name material: a user name cannot carry it, so
# a user def can never collide with a machine-minted name.
# ported from bend3
assert foo:
  Unit

def foo$bar(): Unit{}

assert main:
  Unit

def main(): foo$bar
$$ bend %
Error:
- expected : '('
- observed : '$'
Location:
6 | 
7>| def foo$bar(): Unit{}
8 |
