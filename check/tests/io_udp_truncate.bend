# io (io_udp_truncate): SPEC 1.8's datagram boundary -- a long
# datagram truncates, never splits. Two datagrams queue on the bound
# socket; recv_from at max 3 answers the first one's head ("012")
# and its tail is discarded with it, so the next recv answers the
# second datagram whole ("tail-intact"), never the remainder: the
# pin holds both kits to the datagram boundary, and a buffered
# rewrite that carved streams out of datagrams reds the second row
# (a kit reading past max reds the first). Handles thread back
# OUTSIDE the Result, tuples destructure in their own helpers, and
# the binder retries upward from a base port (+port licenses the
# port's reuse). The recv buffers allocate through the codec guard
# (the csrc pin holds this file's recv site).
# csrc has: io_mem(malloc((uint64_t)max + 1))
import Base

assert send_go:
  forall m: Socket & Result<U32 & String, Unit>
  IO(Socket)

def send_go(m):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

assert data_end:
  forall s: Socket
  forall p: String & U32 & String
  IO(Socket & String)

def data_end(s, p):
  (host, from, data) = p
  IO.pure(Socket & String, (s, data))

assert data_go:
  forall m: Socket & Result<U32 & String, String & U32 & String>
  IO(Socket & String)

def data_go(m):
  (s, r) = m
  do IO<Socket & String>:
    p : String & U32 & String <- IO.pass(String & U32 & String, r)
    data_end(s, p)

assert recv_end:
  forall s2: Socket
  forall q: Socket & String
  IO(U32)

def recv_end(s2, q):
  (s1, d2) = q
  do IO<U32>:
    w : Unit <- IO.print(d2)
    x : Unit <- Socket.close(s1)
    y : Unit <- Socket.close(s2)
    return 0

assert recv_two:
  forall s2: Socket
  forall q: Socket & String
  IO(U32)

def recv_two(s2, q):
  (s1, d1) = q
  do IO<U32>:
    w : Unit <- IO.print(d1)
    m : Socket & Result<U32 & String, String & U32 & String> <- UDP.recv_from(s1, 64)
    q2 : Socket & String <- data_go(m)
    recv_end(s2, q2)

assert recv_one:
  forall s1: Socket
  forall s2: Socket
  IO(U32)

def recv_one(s1, s2):
  do IO<U32>:
    m : Socket & Result<U32 & String, String & U32 & String> <- UDP.recv_from(s1, 3)
    q : Socket & String <- data_go(m)
    recv_two(s2, q)

assert sends_end:
  forall p1: U32
  forall s1: Socket
  forall s2: Socket
  IO(U32)

def sends_end(p1, s1, s2):
  do IO<U32>:
    sm : Socket & Result<U32 & String, Unit> <- UDP.send_to(s2, "127.0.0.1", p1, "tail-intact")
    s2b : Socket <- send_go(sm)
    recv_one(s1, s2b)

assert main_go2:
  forall +p1: +U32
  forall s1: Socket
  forall b: Socket & U32
  IO(U32)

def main_go2(p1, s1, b):
  (s2, p2) = b
  do IO<U32>:
    sm : Socket & Result<U32 & String, Unit> <- UDP.send_to(s2, "127.0.0.1", p1, "0123456789")
    s2b : Socket <- send_go(sm)
    sends_end(p1, s1, s2b)

assert main_go:
  forall a: Socket & U32
  forall b: Socket & U32
  IO(U32)

def main_go(a, b):
  (s1, p1) = a
  main_go2(p1, s1, b)

assert udp_retry:
  forall port: U32
  forall r: Result<U32 & String, Socket>
  forall rest: IO(Socket & U32)
  IO(Socket & U32)

def udp_retry(port, r, rest):
  match r:
    case Done{s}:
      IO.pure(Socket & U32, (s, port))
    case Fail{e}:
      rest

assert udp_bind_any:
  forall tries: Nat
  forall +port: +U32
  IO(Socket & U32)

def udp_bind_any(tries, port):
  match tries:
    case 0n:
      IO.die(Socket & U32, 1, "no free udp port")
    case 1n+t:
      rest = udp_bind_any(t, port + 1)
      do IO<Socket & U32>:
        r : Result<U32 & String, Socket> <- UDP.bind(port)
        udp_retry(port, r, rest)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : Socket & U32 <- udp_bind_any(32n, 19213)
    b : Socket & U32 <- udp_bind_any(32n, 19253)
    main_go(a, b)
$$ bend %
012
tail-intact
$$ bend % --seq
012
tail-intact
exit 0
$$ bend % --par
012
tail-intact
exit 0
$$ bend % --js
012
tail-intact
exit 0
