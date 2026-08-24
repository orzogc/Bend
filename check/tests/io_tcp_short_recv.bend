# io (io_tcp_short_recv): the stream half of SPEC 1.8's read laws.
# A six-byte send read at max 3 answers "abc" and KEEPS the
# remainder in the stream, so the next recv answers "def" -- the
# datagram contrast of io_udp_truncate: a stream discards nothing.
# After the peer's orderly close a recv answers Done with the empty
# payload ("end:" prints bare), the law's own words, never a Fail:
# a kit turning the zero-byte read into an error reds the last row.
# Handles thread back OUTSIDE the Result, tuples destructure in
# their own helpers, and the listener retries upward from a base
# port (+port licenses the port's reuse). The recv buffer allocates
# through the codec guard (the csrc pin holds this file's recv
# site).
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

assert step_four:
  forall l: Listener
  forall m: Socket & Result<U32 & String, String>
  IO(U32)

def step_four(l, m):
  (a, r) = m
  do IO<U32>:
    d3 : String <- IO.pass(String, r)
    w : Unit <- IO.print(String.append("end:", d3))
    y : Unit <- Socket.close(a)
    z : Unit <- Listener.close(l)
    return 0

assert step_three:
  forall l: Listener
  forall c: Socket
  forall m: Socket & Result<U32 & String, String>
  IO(U32)

def step_three(l, c, m):
  (a, r) = m
  do IO<U32>:
    d2 : String <- IO.pass(String, r)
    w : Unit <- IO.print(d2)
    x : Unit <- Socket.close(c)
    rm : Socket & Result<U32 & String, String> <- TCP.recv(a, 64)
    step_four(l, rm)

assert step_two:
  forall l: Listener
  forall c: Socket
  forall m: Socket & Result<U32 & String, String>
  IO(U32)

def step_two(l, c, m):
  (a, r) = m
  do IO<U32>:
    d1 : String <- IO.pass(String, r)
    w : Unit <- IO.print(d1)
    rm : Socket & Result<U32 & String, String> <- TCP.recv(a, 64)
    step_three(l, c, rm)

assert step_accept:
  forall c: Socket
  forall p: Listener & Result<U32 & String, Socket>
  IO(U32)

def step_accept(c, p):
  (l, ar) = p
  do IO<U32>:
    a : Socket <- IO.pass(Socket, ar)
    sm : Socket & Result<U32 & String, Unit> <- TCP.send(c, "abcdef")
    c2 : Socket <- send_go(sm)
    rm : Socket & Result<U32 & String, String> <- TCP.recv(a, 3)
    step_two(l, c2, rm)

assert main_go:
  forall b: Listener & U32
  IO(U32)

def main_go(b):
  (l, port) = b
  do IO<U32>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    p : Listener & Result<U32 & String, Socket> <- TCP.accept(l)
    step_accept(c, p)

assert tcp_retry:
  forall port: U32
  forall r: Result<U32 & String, Listener>
  forall rest: IO(Listener & U32)
  IO(Listener & U32)

def tcp_retry(port, r, rest):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

assert tcp_listen_any:
  forall tries: Nat
  forall +port: +U32
  IO(Listener & U32)

def tcp_listen_any(tries, port):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free tcp port")
    case 1n+t:
      rest = tcp_listen_any(t, port + 1)
      do IO<Listener & U32>:
        r : Result<U32 & String, Listener> <- TCP.listen(port)
        tcp_retry(port, r, rest)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    b : Listener & U32 <- tcp_listen_any(32n, 19647)
    main_go(b)
$$ bend %
abc
def
end:
$$ bend % --seq
abc
def
end:
exit 0
$$ bend % --par
abc
def
end:
exit 0
$$ bend % --js
abc
def
end:
exit 0
