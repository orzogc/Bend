# io pin (io_fiber_boxed_join): bend3's boxed twin of hello -- a forked
# fiber yields a String, so the child's terminal Emit took the BOXED
# row through the driver's dispatch. bend4 has no driver, and fibers
# wait for V2 -- main dies on the missing Fiber type.
import Base

assert child:
  IO(String)

def child():
  IO.pure(String, "boxed")

assert main:
  IO(U32)

def main():
  do IO<U32>:
    t : Fiber<String> <- IO.fork(String, child())
    s : String <- IO.join(String, t)
    x : Unit <- IO.print(s)
    return 0
$$ bend %
Error:
- message  : a declared datatype (unknown: Fiber)
Location: main
17 |   do IO<U32>:
18>|     t : Fiber<String> <- IO.fork(String, child())
19 |     s : String <- IO.join(String, t)
