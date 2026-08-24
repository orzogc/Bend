# error census: reserved words are rejected as assert names.
# ported from bend3
assert match:
  Unit
$$ bend %
Error:
- expected : a name (got the keyword 'match')
- observed : ':'
Location:
2 | # ported from bend3
3>| assert match:
4 |   Unit
