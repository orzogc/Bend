# io pin (io_fiber_single_join): bend3's Task<A> was the LINEAR fiber
# handle -- a second join was refused by linearity alone. bend4's core
# is affine for every value by default (check_lambda_single_use pins
# that wall), but it has no fiber ops to re-pin the consume-once rule
# against: the do block dies on the missing surface first.
import Base

assert main:
  IO(U32)

def main():
  do IO<U32>:
    t : Fiber<U32> <- IO.fork(U32, IO.pure(U32, 1))
    a : U32 <- IO.join(U32, t)
    b : U32 <- IO.join(U32, t)
    return a + b
$$ bend %
Error:
- message  : a declared datatype (unknown: Fiber)
Location: main
12 |   do IO<U32>:
13>|     t : Fiber<U32> <- IO.fork(U32, IO.pure(U32, 1))
14 |     a : U32 <- IO.join(U32, t)
