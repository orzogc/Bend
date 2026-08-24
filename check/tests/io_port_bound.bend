# io (io_port_bound): a port is at most 65535, one law in both kits'
# address codec, and a port past it answers Fail(EINVAL) at every
# port-taking op in every backend. Both kits once truncated the port
# to 16 bits silently: TCP.listen(65536) and UDP.bind(65536) bound
# port 0, so the kernel picked an ephemeral port and the program
# SUCCEEDED on a port it never asked for, and connect and send_to
# dialed the wrapped port. The boundary stays legal: the 65535
# datagram sends.
import Base

assert opened:
  forall r: Result<U32 & String, Socket>
  IO(Unit)

def opened(r):
  match r:
    case Done{value}:
      do IO<Unit>:
        p : Unit <- IO.print("opened")
        Socket.close(value)
    case Fail{error}:
      (code, message) = error
      IO.print(message)

assert served:
  forall r: Result<U32 & String, Listener>
  IO(Unit)

def served(r):
  match r:
    case Done{value}:
      do IO<Unit>:
        p : Unit <- IO.print("served")
        Listener.close(value)
    case Fail{error}:
      (code, message) = error
      IO.print(message)

assert posted:
  forall m: Socket & Result<U32 & String, Unit>
  IO(Socket)

def posted(m):
  (s, r) = m
  match r:
    case Done{value}:
      do IO<Socket>:
        p : Unit <- IO.print("sent")
        return s
    case Fail{error}:
      (code, message) = error
      do IO<Socket>:
        p : Unit <- IO.print(message)
        return s

assert probe:
  forall s: Socket
  forall host: String
  forall port: U32
  IO(Socket)

def probe(s, host, port):
  do IO<Socket>:
    m : Socket & Result<U32 & String, Unit> <- UDP.send_to(s, host, port, "x")
    posted(m)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : Result<U32 & String, Socket> <- UDP.bind(65536)
    p : Unit <- opened(a)
    b : Result<U32 & String, Listener> <- TCP.listen(65536)
    q : Unit <- served(b)
    c : Result<U32 & String, Socket> <- TCP.connect("127.0.0.1", 4294967295)
    r : Unit <- opened(c)
    s : Socket <- IO.try(Socket, UDP.bind(0))
    t : Socket <- probe(s, "127.0.0.1", 65536)
    u : Socket <- probe(t, "127.0.0.1", 65535)
    x : Unit <- Socket.close(u)
    return 0
$$ bend %
Invalid argument
Invalid argument
Invalid argument
Invalid argument
sent
$$ bend % --seq
Invalid argument
Invalid argument
Invalid argument
Invalid argument
sent
exit 0
$$ bend % --par
Invalid argument
Invalid argument
Invalid argument
Invalid argument
sent
exit 0
$$ bend % --js
Invalid argument
Invalid argument
Invalid argument
Invalid argument
sent
exit 0
