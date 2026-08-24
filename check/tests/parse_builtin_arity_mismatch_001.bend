# bend3's $-builtin arity error; bend4 has no builtin sigil and the
# F32 math lib is ruled out entirely, so the sqrt call dies on the
# undefined name's position
import Base

assert main:
  F32

def main():
  F32.sqrt(1.0, 2.0)
$$ bend %
Error:
- expected : a function type
- observed : F32
Location: main
 9 | def main():
10>|   F32.sqrt(1.0, 2.0)
11 |
