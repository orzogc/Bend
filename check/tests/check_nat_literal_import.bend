# nat literals are UNGATED sugar over the Zero/Succ constructors: with
# no declaration in scope, 2n fails as an unknown constructor, never as
# a parse error.
# ported from bend3: bend3 gated the literal on `import Nat`; bend4's
# sugar always parses and resolves against the book
assert main:
  Type

def main():
  x = 2n
  Type
$$ bend %
Error:
- expected : a declared constructor
- observed : 2n
Location: main
 9 | def main():
10>|   x = 2n
11 |   Type
