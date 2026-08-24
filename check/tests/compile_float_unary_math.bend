# no exp/log: ruled out of base (sqrt alone stands); the name is
# unbound
import Base

assert main:
  F32

def main():
  F32.exp(1.0)
$$ bend %
Error:
- expected : a defined name
- observed : F32.exp
Location: main
 8 | def main():
 9>|   F32.exp(1.0)
10 |
