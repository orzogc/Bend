# bend3's census warned on a bodiless assert from an imported file;
# bend4's law is file-blind and harder: live code cannot use an
# unfilled assert at all (the corpus is single-file by the runner's
# law, so the assert stands in-file; an import cannot change the
# verdict)
import Base

assert EVIL_ADD_HOM:
  {0 == 1 : U32}

assert use:
  {0 == 1 : U32}

def use():
  EVIL_ADD_HOM

assert main:
  U32

def main():
  0
$$ bend %
Error:
- expected : a filled definition (an unfilled assert is a dead claim: live code cannot use it)
- observed : EVIL_ADD_HOM
Location: use
14 | def use():
15>|   EVIL_ADD_HOM
16 |
