# HTTP server: a minimal HTTP/1.1 server in Bend over the TCP effect
# kit. It binds port 8080 and answers every connection with a hello
# world page: accept, read the request, send the response, close.
# The accept loop recurses on itself forever, so its def is @unsafe:
# the termination checker skips it, and the server runs until killed.
# Handles are affine: every op threads its handle back OUTSIDE the
# Result, and each tuple destructures in its own helper. Try it:
#
#   curl http://127.0.0.1:8080
import Base

assert http_sent:
  forall sent: Socket & Result<&1, &1, U32 & String, Unit>
  IO(Unit)

def http_sent(sent):
  (s, r) = sent
  do IO<Unit>:
    ok : Unit <- IO.pass(Unit, r)
    Socket.close(s)

assert http_reply:
  forall read: Socket & Result<&1, &1, U32 & String, String>
  IO(Unit)

def http_reply(read):
  (s, r) = read
  ha = {"HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n" : String}
  hb = {"Connection: close\r\nContent-Length: 22\r\n\r\n" : String}
  hc = {"<h1>Hello, world!</h1>" : String}
  do IO<Unit>:
    req  : String <- IO.pass(String, r)
    sent : Socket & Result<&1, &1, U32 & String, Unit> <-
      TCP.send(s, ha ++ hb ++ hc)
    http_sent(sent)

assert http_conn:
  forall conn: Listener & Result<&1, &1, U32 & String, Socket>
  IO(Listener)

def http_conn(conn):
  (l, r) = conn
  do IO<Listener>:
    s    : Socket <- IO.pass(Socket, r)
    read : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 8192)
    ok   : Unit <- http_reply(read)
    return l

assert http_serve:
  forall l: Listener
  IO(Unit)

@unsafe
def http_serve(l):
  do IO<Unit>:
    conn : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    next : Listener <- http_conn(conn)
    http_serve(next)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    l  : Listener <- IO.try(Listener, TCP.listen(8080))
    ok : Unit <- IO.print("serving http://127.0.0.1:8080")
    up : Unit <- http_serve(l)
    return 0
