# the comma parallel let is not grammar: a bend4 let binds ONE name (or
# one ctor pattern), so `a, b = v` fails at the comma.
# ported from bend3: bend3 pinned the let-arity page of its fork let;
# bend4 has no comma let at all, so the port pins the refusal
import Base

assert f:
  forall x: U32
  U32

def f(x):
  x

assert main:
  U32

def main():
  a, b = f(1)
  a
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : ','
Location:
17 | def main():
18>|   a, b = f(1)
19 |   a
