# io (io_udp_send_recv): bend3's recv_from stamped each datagram with
# its sender, and send_to consumed exactly that stamp -- replying is
# echoing the address back. bend4 pins the same protocol whole: two
# sockets, a ping from the first, a reply from the second to the
# stamp it received, the pong printed off the first. Every op
# threads its handle back OUTSIDE the Result (no path can lose it),
# tuples destructure in helpers, binds retry upward on Fail: the
# fallback action is built before the attempt, so the retry is a
# plain value and the recursion is a structural descent on tries
# (+port licenses the port's reuse).
import Base

assert send_go:
  forall m: Socket & Result<U32 & String, Unit>
  IO(Socket)

def send_go(m):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

assert finish_end:
  forall s1: Socket
  forall s2: Socket
  forall p: String & U32 & String
  IO(U32)

def finish_end(s1, s2, p):
  (host, from, data) = p
  do IO<U32>:
    w : Unit <- IO.print(data)
    x : Unit <- Socket.close(s1)
    y : Unit <- Socket.close(s2)
    return 0

assert finish_go:
  forall s2: Socket
  forall m: Socket & Result<U32 & String, String & U32 & String>
  IO(U32)

def finish_go(s2, m):
  (s1, r) = m
  do IO<U32>:
    p : String & U32 & String <- IO.pass(String & U32 & String, r)
    finish_end(s1, s2, p)

assert reply_end:
  forall s1: Socket
  forall s2: Socket
  forall p: String & U32 & String
  IO(U32)

def reply_end(s1, s2, p):
  (host, from, data) = p
  do IO<U32>:
    sm : Socket & Result<U32 & String, Unit> <- UDP.send_to(s2, host, from, String.append(data, "-pong"))
    s2b : Socket <- send_go(sm)
    rm : Socket & Result<U32 & String, String & U32 & String> <- UDP.recv_from(s1, 64)
    finish_go(s2b, rm)

assert reply_go:
  forall s1: Socket
  forall m: Socket & Result<U32 & String, String & U32 & String>
  IO(U32)

def reply_go(s1, m):
  (s2, r) = m
  do IO<U32>:
    p : String & U32 & String <- IO.pass(String & U32 & String, r)
    reply_end(s1, s2, p)

assert main_go2:
  forall s1: Socket
  forall b: Socket & U32
  IO(U32)

def main_go2(s1, b):
  (s2, p2) = b
  do IO<U32>:
    sm : Socket & Result<U32 & String, Unit> <- UDP.send_to(s1, "127.0.0.1", p2, "bend-udp")
    s1b : Socket <- send_go(sm)
    m : Socket & Result<U32 & String, String & U32 & String> <- UDP.recv_from(s2, 64)
    reply_go(s1b, m)

assert main_go:
  forall a: Socket & U32
  forall b: Socket & U32
  IO(U32)

def main_go(a, b):
  (s1, p1) = a
  main_go2(s1, b)

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
    a : Socket & U32 <- udp_bind_any(32n, 19053)
    b : Socket & U32 <- udp_bind_any(32n, 19073)
    main_go(a, b)
$$ bend %
bend-udp-pong
$$ bend % --seq
bend-udp-pong
exit 0
$$ bend % --par
bend-udp-pong
exit 0
$$ bend % --js
bend-udp-pong
exit 0
