# error census: a trailing bind line (no continuation) is rejected -- a
# bind needs a rest to feed.
# ported from bend3: Base's Result, bend4 error page
import Base

assert f:
  Result<Unit, U32>

def f():
  do Result<Unit, U32>:
    x <- Result.pure(Unit, U32, 1)
$$ bend %
Error:
- expected : a term
- observed : end of input
Location:
11 |     x <- Result.pure(Unit, U32, 1)
12>|
