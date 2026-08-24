# refusal pin: bend3's --no-halt door let use2 duplicate a value of the
# FORWARD datatype D, and the pin was that an unchecked datatype must
# never certify Data-ness. bend4 has no --no-halt door: names resolve
# upward only in a strict file, so the forward D3 in Two's field is
# itself the refusal -- the duplication in use2 is never weighed.
# ported from bend3: the Pair.Pair redefinition half is pinned by
# check_data_table_checked_000 (the duplicate-declaration wall)
import Base

type Two:
  MkTwo{a: D3<U32>, b: D3<U32>}

assert use2:
  forall x: D3<U32>
  Two

def use2(x):
  MkTwo{x, x}

type D3<result: Type>:
  MkD3{fun: D3<result> -> result}

assert main:
  U32

def main(): 0
$$ bend %
Error:
- message  : a declared datatype (unknown: D3)
Location:
10 | type Two:
11>|   MkTwo{a: D3<U32>, b: D3<U32>}
12 | 
