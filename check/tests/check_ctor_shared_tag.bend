# bend3 scoped ctor tags per datatype and resolved by expected type;
# bend4's tags are global and unique by design -- the shared K dies at
# its second declaration
import Base

type A5:
  K5{}

type B5:
  K5{a: A5}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a fresh constructor name (duplicate declaration: K5)
- observed : '{'
Location:
 9 | type B5:
10>|   K5{a: A5}
11 | 
