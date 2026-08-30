# HTTP server: a minimal HTTP/1.1 server in Bend over the TCP effect
# kit. It binds port 8080 and answers every connection with a hello
# world page: accept, read the request, send the response, close.
# Bend is total, so the accept loop is not `while (true)`: it descends
# on a Nat fuel, one unit per connection -- a billion connections
# (U32.to_nat keeps the numeral native) make the server persistent in
# practice. Handles are affine: every op
# threads its handle back OUTSIDE the Result, and each tuple
# destructures in its own helper. Try it:
#
#   curl http://127.0.0.1:8080
import Base

assert http_sent:
  forall sm: Socket & Result<&1, &1, U32 & String, Unit>
  IO(Unit)

def http_sent(sm):
  (s, r) = sm
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    Socket.close(s)

assert http_reply:
  forall rm: Socket & Result<&1, &1, U32 & String, String>
  IO(Unit)

def http_reply(rm):
  (s, r) = rm
  ha = {"HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n" : String}
  hb = {"Connection: close\r\nContent-Length: 22\r\n\r\n" : String}
  hc = {"<h1>Hello, world!</h1>" : String}
  do IO<Unit>:
    req : String <- IO.pass(String, r)
    sm : Socket & Result<&1, &1, U32 & String, Unit> <-
      TCP.send(s, ha ++ hb ++ hc)
    http_sent(sm)

assert http_conn:
  forall ap: Listener & Result<&1, &1, U32 & String, Socket>
  IO(Listener)

def http_conn(ap):
  (l, ar) = ap
  do IO<Listener>:
    s : Socket <- IO.pass(Socket, ar)
    rm : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 8192)
    u : Unit <- http_reply(rm)
    return l

assert http_serve:
  forall n: Nat
  forall l: Listener
  IO(Unit)

def http_serve(n, l):
  match n:
    case 0n:
      Listener.close(l)
    case 1n+m:
      do IO<Unit>:
        ap : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
        l2 : Listener <- http_conn(ap)
        http_serve(m, l2)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    l : Listener <- IO.try(Listener, TCP.listen(8080))
    u : Unit <- IO.print("serving http://127.0.0.1:8080")
    v : Unit <- http_serve(U32.to_nat(1000000000), l)
    return 0
