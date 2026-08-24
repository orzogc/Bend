# the ctor-pattern bind `P{..} <- e` is dead syntax: `<-` lives only in
# do-blocks; an upper-head statement is `P{..} = e`.
# ported from bend3
import Base

type Pw:
  Pp{a: U32, b: U32}

assert go:
  forall k: Pw
  U32

def go(k):
  Pp{a, b} <- k
  a

assert main:
  U32

def main(): go(Pp{1, 2})
$$ bend %
Error:
- expected : 'def', 'type' or 'assert'
- observed : '<'
Location:
13 | def go(k):
14>|   Pp{a, b} <- k
15 |   a
