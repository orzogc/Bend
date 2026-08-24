# a datatype whose field reaches a closure (through a nested datatype)
# is affine like everything else: over-using a Badd binder is rejected
# at the second use.
# ported from bend3
import Base

type Bxd:
  Bd{f: U32 -> U32}

type Badd:
  Wd{b: Bxd}

assert idd:
  forall x: U32
  U32

def idd(x): x

assert mk:
  Badd

def mk(): Wd{Bd{idd}}

assert use:
  forall b: Badd
  U32

def use(b): 0

assert main:
  U32

def main():
  b = mk()
  U32.add(use(b), use(b))
$$ bend %
Error:
- expected : b
- observed : b (consumed more than once)
Location: main
33 | def main():
34>|   b = mk()
35 |   U32.add(use(b), use(b))
