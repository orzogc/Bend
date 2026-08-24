# audit: indexed constructor result annotations are rejected until
# indexed elimination exists -- the whitespace-mashed spelling hits the
# same page (layout-free).
# ported from bend3
type Ix2<n:Nat>:
  I0x{}:Ix2(0n)
assert main:
  Unit

def main():Unit{}
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
5 | type Ix2<n:Nat>:
6>|   I0x{}:Ix2(0n)
7 | assert main:
