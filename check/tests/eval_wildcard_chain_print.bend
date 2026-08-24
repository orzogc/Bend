# wildcard lambda chains: each _ binds fresh, all display as _.
# ported from bend3: the body becomes 5n for a readable golden
import Base

assert main:
  @x:U32 -> @y:U32 -> Nat

def main():
  _ => _ => 5n
$$ bend %
_ => _ => 5n
