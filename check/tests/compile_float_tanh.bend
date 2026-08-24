# no tanh: the F32 math lib is ruled out of base, and the name is
# simply unbound
import Base

assert main:
  F32

def main():
  F32.tanh(1.0)
$$ bend %
Error:
- expected : a defined name
- observed : F32.tanh
Location: main
 8 | def main():
 9>|   F32.tanh(1.0)
10 |
