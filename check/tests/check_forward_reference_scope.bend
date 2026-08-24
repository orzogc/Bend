# bend3's C27 let a def between an assert and its fill call the
# asserted name; bend4 refuses by design -- a def may not use a
# demanded name (only asserts may), and the refusal names the law
import Base

assert foo:
  forall x: U32
  U32

assert bar:
  U32

def bar():
  foo(1)

def foo(x):
  x

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : foo
Location: bar
13 | def bar():
14>|   foo(1)
15 |
