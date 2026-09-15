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
#   bend demos/io_tcp_echos/main.bend -o echos && ./echos
#   nc 127.0.0.1 7777
import Base

# Spec
# ====
# The connection as a pure function of the frames it reads. A frame is
# the data of one recv as echo_data reads it: "" for a closed peer or
# a failed recv. echo_step decides a frame (send it back, or close),
# and echo(frames) is what the connection sends for a list of frames,
# in order: the step echo_conn runs, frame by frame. LAWS.bend states
# what they guarantee; PROOF.bend proves it.

# the data of a recv: a failure reads as a closed peer
def echo_data(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{data}:
      data
    case Fail{e}:
      SNil{}

# a frame's move: its data sent back, or nothing: the connection closes
def echo_step(d: String) -> Maybe<String>:
  match d:
    case SNil{}:
      None{}
    case SCon{h, t}:
      Some{SCon{h, t}}

# the frames sent after a move: the data, then the rest; or nothing
def echo_go(m: Maybe<String>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{d}:
      d <> rest

# what the connection sends for the frames it reads, in order
def echo(frames: List<&2, String>) -> List<&2, String>:
  match frames:
    case Nil{}:
      []
    case d <> rest:
      echo_go(echo_step(d), echo(rest))

# does every frame carry data (the peer never closed)
def all_data(frames: List<&2, String>) -> Bool:
  match frames:
    case Nil{}:
      True{}
    case SNil{} <> rest:
      False{}
    case SCon{c, t} <> rest:
      all_data(rest)

def cat(a: List<&2, String>, b: List<&2, String>) -> List<&2, String>:
  match a:
    case Nil{}:
      b
    case d <> rest:
      d <> cat(rest, b)

# the bytes of the frames, in order
def concat(frames: List<&2, String>) -> String:
  match frames:
    case Nil{}:
      ""
    case d <> rest:
      d ++ concat(rest)

# Server
# ======

def send_go(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Socket):
  (s, r) = m
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

# the move made: the data sent and the handler goes on, or the close
def echo_send(s: Socket, m: Maybe<String>, next: Socket -> IO(Unit)) -> IO(Unit):
  match m:
    case None{}:
      Socket.close(s)
    case Some{d}:
      do IO<Unit>:
        sm : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(s, d)
        s2 : Socket <- send_go(sm)
        next(s2)

def echo_back(m: Socket & Result<&1, &1, U32 & String, String>, next: Socket -> IO(Unit)) -> IO(Unit):
  (s, r) = m
  echo_send(s, echo_step(echo_data(r)), next)

@unsafe
def echo_conn(s: Socket) -> IO(Unit):
  do IO<Unit>:
    rm : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 4096)
    echo_back(rm, s2 => echo_conn(s2))

def serve_next(p: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Listener):
  (l, r) = p
  do IO<Listener>:
    s : Socket <- IO.pass(Socket, r)
    Unit <- IO.spawn(Unit, echo_conn(s))
    return l

@unsafe
def serve(l: Listener) -> IO(Unit):
  do IO<Unit>:
    p  : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    l2 : Listener <- serve_next(p)
    serve(l2)

def main() -> IO(U32):
  do IO<U32>:
    l  : Listener <- IO.try(Listener, TCP.listen(7777))
    ok : Unit <- IO.print("echoing on 127.0.0.1:7777")
    up : Unit <- serve(l)
    return 0
