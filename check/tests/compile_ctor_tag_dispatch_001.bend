# bend3's red-team pin made duplicate ctor names across datatypes
# LEGAL (resolution via the expected type); bend4 inverts the law by
# design -- constructors are bare and globally unique, and the second
# Mk dies at declaration
import Base

type A8:
  Mk8b{v: U32}

type B8:
  Mk8b{v: U32, w: U32}

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a fresh constructor name (duplicate declaration: Mk8b)
- observed : '{'
Location:
10 | type B8:
11>|   Mk8b{v: U32, w: U32}
12 | 
