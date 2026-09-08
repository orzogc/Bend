# Echo server: a computation per connection over the TCP effect kit.
# It binds port 7777 and accepts forever (the accept loop is @unsafe:
# it runs until killed); each accepted socket goes to IO.spawn, so its
# handler runs as a computation of its own, echoing what it reads
# until the peer closes. A recv or an accept with nothing to read
# parks only its own computation on the event loop's poller and the
# loop runs the others, so every client is served at once on one
# thread. Handles are affine and thread back OUTSIDE the Result; each
# tuple destructures in its own helper. The twins beside it (echo.c:
# kqueue/epoll) and the load generator (load.c: N
# connections, M round trips of 64 bytes) measure it. Try it:
#
#   nc 127.0.0.1 7777
import Base

law send_go:
  for m: Socket & Result<&1, &1, U32 & String, Unit>
  IO(Socket)

def send_go(m):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

law echo_back:
  for m    : Socket & Result<&1, &1, U32 & String, String>
  for next : Socket -> IO(Unit)
  IO(Unit)

def echo_back(m, next):
  (s, r) = m
  match r:
    case Done{data}:
      match data:
        case SNil{}:
          Socket.close(s)
        case SCon{h, t}:
          do IO<Unit>:
            sm : Socket & Result<&1, &1, U32 & String, Unit> <-
              TCP.send(s, SCon{h, t})
            s2 : Socket <- send_go(sm)
            next(s2)
    case Fail{e}:
      Socket.close(s)

law echo_conn:
  for s: Socket
  IO(Unit)

@unsafe
def echo_conn(s):
  do IO<Unit>:
    rm : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 4096)
    echo_back(rm, s2 => echo_conn(s2))

law serve_next:
  for p: Listener & Result<&1, &1, U32 & String, Socket>
  IO(Listener)

def serve_next(p):
  (l, r) = p
  do IO<Listener>:
    s : Socket <- IO.pass(Socket, r)
    Unit <- IO.spawn(Unit, echo_conn(s))
    return l

law serve:
  for l: Listener
  IO(Unit)

@unsafe
def serve(l):
  do IO<Unit>:
    p  : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    l2 : Listener <- serve_next(p)
    serve(l2)

law main:
  IO(U32)

def main():
  do IO<U32>:
    l  : Listener <- IO.try(Listener, TCP.listen(7777))
    ok : Unit <- IO.print("echoing on 127.0.0.1:7777")
    up : Unit <- serve(l)
    return 0
