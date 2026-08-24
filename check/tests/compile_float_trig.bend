# no trig: F32.sin and kin are ruled out of base; the name is unbound
import Base

assert main:
  F32

def main():
  F32.sin(1.0)
$$ bend %
Error:
- expected : a defined name
- observed : F32.sin
Location: main
7 | def main():
8>|   F32.sin(1.0)
9 |
