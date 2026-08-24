# no $-sigiled float builtins and no floor: bend4 has no builtin
# surface at all -- the name is unbound (bend3 pinned its builtin
# arity errors)
import Base

assert main:
  F32

def main():
  F32.floor(1.5)
$$ bend %
Error:
- expected : a defined name
- observed : F32.floor
Location: main
 9 | def main():
10>|   F32.floor(1.5)
11 |
