# bend3 scoped ctor tags per datatype (two types sharing K at
# different arities); bend4 ctor names are global and unique by
# design, so the shared tag is refused at its second declaration
import Base

type A7:
  K7{a: U32}
  E7{}

type B7b:
  K7{a: U32, b: U32}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a fresh constructor name (duplicate declaration: K7)
- observed : '{'
Location:
10 | type B7b:
11>|   K7{a: U32, b: U32}
12 | 
