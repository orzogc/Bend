# audit: constructor targets cannot change datatype parameters -- a ctor
# row takes no result annotation at all.
# ported from bend3: params move to bend4's angle group
type Dd<n: Nat, A: Type>:
  Cc{} : Dd(n, @x: Type -> x)

assert main:
  Unit

def main(): Unit{}
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ':'
Location:
4 | type Dd<n: Nat, A: Type>:
5>|   Cc{} : Dd(n, @x: Type -> x)
6 | 
