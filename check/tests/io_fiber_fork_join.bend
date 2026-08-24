# io pin (io_fiber_fork_join): bend3 pinned the whole fiber protocol
# residual -- fork/join/race/spawn as plain wrappers over the
# scheduler's Op constructors. bend4 dropped the fiber protocol whole
# -- fibers and channels wait for V2 -- so the do block dies on the
# missing Fiber type.
import Base

assert main:
  IO(U32)

def main():
  do IO<U32>:
    t : Fiber<Unit> <- IO.fork(Unit, IO.sleep(5))
    a : Unit <- IO.join(Unit, t)
    b : U32 <- IO.race(U32, IO.pure(U32, 1), IO.pure(U32, 9))
    u : Unit <- IO.spawn(IO.pure(Unit, Unit{}))
    return b
$$ bend %
Error:
- message  : a declared datatype (unknown: Fiber)
Location: main
12 |   do IO<U32>:
13>|     t : Fiber<Unit> <- IO.fork(Unit, IO.sleep(5))
14 |     a : Unit <- IO.join(Unit, t)
