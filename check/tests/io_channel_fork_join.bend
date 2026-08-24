# io pin (io_channel_fork_join): bend3 fed a bounded channel from a
# spawned producer, recv'd both in order, then fork/join round-tripped
# a value (exit 5). bend4 dropped the channel protocol whole -- fibers
# and channels wait for V2 -- so producer's do block dies on the
# missing types first (Chan<A> respells as Sender & Receiver).
import Base

assert producer:
  forall c: Sender<U32> & Receiver<U32>
  IO(Unit)

def producer(c):
  do IO<Unit>:
    a : Result<U32, Sender<U32>> <- Chan.send(U32, c, 11)
    b : Result<U32, Sender<U32>> <- Chan.send(U32, c, 22)
    k : Unit <- Chan.close(U32, c)
    return Unit{}

assert main:
  IO(U32)

def main():
  do IO<U32>:
    c : Sender<U32> & Receiver<U32> <- Chan.new(U32, 4)
    u : Unit <- IO.spawn(producer(c))
    x : U32 <- IO.try(U32, Chan.recv(U32, c))
    y : U32 <- IO.try(U32, Chan.recv(U32, c))
    z : Unit <- IO.print(U32.show(x * 100 + y))
    t : Fiber<U32> <- IO.fork(U32, IO.pure(U32, 5))
    w : U32 <- IO.join(U32, t)
    return w
$$ bend %
Error:
- message  : a declared datatype (unknown: Sender)
Location:
 8 | assert producer:
 9>|   forall c: Sender<U32> & Receiver<U32>
10 |   IO(Unit)
