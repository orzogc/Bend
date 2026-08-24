# audit: constructor result arrows are rejected instead of being treated
# as fields.
# ported from bend3
type Dd:
  Cc{} : U32 -> Dd

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
4 | type Dd:
5>|   Cc{} : U32 -> Dd
6 | 
