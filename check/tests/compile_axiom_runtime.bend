# proofs erase at compilation, so an axiom (bodiless assert) may never
# reach a runtime position: reaching one is a named error on every lane
# ported from bend3
import Base

assert magic:
  U32

assert main:
  U32

def main():
  magic
$$ bend %
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : magic
Location: main
12 | def main():
13>|   magic
14 |
$$ bend % --seq
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : magic
Location: main
12 | def main():
13>|   magic
14 |
exit 1
$$ bend % --par
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : magic
Location: main
12 | def main():
13>|   magic
14 |
exit 1
$$ bend % --js
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : magic
Location: main
12 | def main():
13>|   magic
14 |
exit 1
