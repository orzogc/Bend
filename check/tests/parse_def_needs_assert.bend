# a def is ONLY the fill of a prior assert: the assert holds the type,
# the def holds bare binders and the body, and a def whose name has no
# prior assert is refused at the head. ported from bend3
def add(x, y):
  x
$$ bend %
Error:
- expected : a prior assert for add (an assert holds the type, a def fills the body)
- observed : '('
Location:
3 | # prior assert is refused at the head. ported from bend3
4>| def add(x, y):
5 |   x
