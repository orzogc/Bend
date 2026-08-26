# HTTP server (SPEC 1.8): a minimal HTTP/1.1 server in Bend over the
# TCP effect kit, plus the loopback client that proves it works. The
# server loop accepts n connections; each one is read, routed on its
# request path, and answered with a valid response -- status line,
# Content-Length, blank line, body -- then closed. The event loop is
# sequential and loopback buffers, so the client opens and sends both
# requests BEFORE the server runs, and reads both responses after it.
# Each response is compared byte for byte against a hand-written
# literal, pinning the response bytes in this file. Handles are
# affine: every op threads its handle back OUTSIDE the Result, each
# tuple destructures in its own helper, and the listener retries
# upward from a base port on Fail -- the fallback action is built
# before the attempt, so the recursion is a structural descent on
# tries (+port licenses the port's reuse).
import Base

assert str_len:
  forall s: String
  U32

def str_len(s):
  match s:
    case SNil{}:
      0
    case SCon{c, t}:
      1 + str_len(t)

assert req_skip.go:
  forall s: String
  forall e: Bool
  String

assert req_skip:
  forall s: String
  String

def req_skip.go(s, e):
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{code}, t}:
      match e:
        case True{}:
          SCon{Chr{code}, t}
        case False{}:
          req_skip.go(t, U32.is_eq(code, 32))

def req_skip(s):
  req_skip.go(s, False{})

assert req_take.sel:
  forall e: Bool
  forall u2: U32
  forall rest: String
  String

assert req_take.cpy:
  forall -code: U32
  forall rest: String
  forall c: Copy(U32, code) & Copy(U32, code)
  String

assert req_take:
  forall s: String
  String

def req_take.sel(e, u2, rest):
  match e:
    case True{}:
      SNil{}
    case False{}:
      SCon{Chr{u2}, rest}

def req_take.cpy(code, rest, c):
  ((u1, e1), (u2, e2)) = c
  req_take.sel(U32.is_eq(u1, 32), u2, rest)

def req_take(s):
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{code}, t}:
      req_take.cpy(code, req_take(t), U32.copy(code))

assert req_path:
  forall req: String
  String

def req_path(req):
  req_take(req_skip(req))

assert http_route.sel:
  forall e: Bool
  String & String

assert http_route:
  forall path: String
  String & String

def http_route.sel(e):
  match e:
    case True{}:
      ("200 OK", "Hello from Bend!")
    case False{}:
      ("404 Not Found", "not found")

def http_route(path):
  http_route.sel(String.eq(path, "/"))

assert http_response.go:
  forall status: String
  forall bb: String & String
  String

assert http_response:
  forall status: String
  forall body: String
  String

def http_response.go(status, bb):
  (b1, b2) = bb
  head = "HTTP/1.1 " ++ status ++ "\r\n"
  size = "Content-Length: " ++ U32.show(str_len(b1)) ++ "\r\n\r\n"
  head ++ size ++ b2

def http_response(status, body):
  http_response.go(status, String.copy(body))

assert http_reply.go:
  forall sb: String & String
  String

assert http_reply:
  forall req: String
  String

def http_reply.go(sb):
  (status, body) = sb
  http_response(status, body)

def http_reply(req):
  http_reply.go(http_route(req_path(req)))

assert http_sent:
  forall sm: Socket & Result<U32 & String, Unit>
  IO(Unit)

def http_sent(sm):
  (s, r) = sm
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    Socket.close(s)

assert http_handle_go:
  forall rm: Socket & Result<U32 & String, String>
  IO(Unit)

def http_handle_go(rm):
  (s, r) = rm
  do IO<Unit>:
    req : String <- IO.pass(String, r)
    sm : Socket & Result<U32 & String, Unit> <- TCP.send(s, http_reply(req))
    http_sent(sm)

assert http_handle:
  forall s: Socket
  IO(Unit)

def http_handle(s):
  do IO<Unit>:
    rm : Socket & Result<U32 & String, String> <- TCP.recv(s, 1024)
    http_handle_go(rm)

assert http_accept_go:
  forall ap: Listener & Result<U32 & String, Socket>
  IO(Listener)

def http_accept_go(ap):
  (l, ar) = ap
  do IO<Listener>:
    s : Socket <- IO.pass(Socket, ar)
    u : Unit <- http_handle(s)
    return l

assert http_serve:
  forall n: Nat
  forall l: Listener
  IO(Listener)

def http_serve(n, l):
  match n:
    case 0n:
      IO.pure(Listener, l)
    case 1n+m:
      do IO<Listener>:
        ap : Listener & Result<U32 & String, Socket> <- TCP.accept(l)
        l2 : Listener <- http_accept_go(ap)
        http_serve(m, l2)

assert http_start_go:
  forall sm: Socket & Result<U32 & String, Unit>
  IO(Socket)

def http_start_go(sm):
  (s, r) = sm
  do IO<Socket>:
    u : Unit <- IO.pass(Unit, r)
    return s

assert http_start:
  forall port: U32
  forall req: String
  IO(Socket)

def http_start(port, req):
  do IO<Socket>:
    c : Socket <- IO.try(Socket, TCP.connect("127.0.0.1", port))
    sm : Socket & Result<U32 & String, Unit> <- TCP.send(c, req)
    http_start_go(sm)

assert http_finish_go:
  forall rm: Socket & Result<U32 & String, String>
  IO(String)

def http_finish_go(rm):
  (s, r) = rm
  do IO<String>:
    resp : String <- IO.pass(String, r)
    u : Unit <- Socket.close(s)
    return resp

assert http_finish:
  forall c: Socket
  IO(String)

def http_finish(c):
  do IO<String>:
    rm : Socket & Result<U32 & String, String> <- TCP.recv(c, 1024)
    http_finish_go(rm)

assert report.sel:
  forall label: String
  forall g2: String
  forall e: Bool
  IO(Unit)

assert report.go:
  forall label: String
  forall want: String
  forall gg: String & String
  IO(Unit)

assert report:
  forall label: String
  forall got: String
  forall want: String
  IO(Unit)

def report.sel(label, g2, e):
  match e:
    case True{}:
      IO.print(label ++ ": exact response bytes")
    case False{}:
      IO.print(label ++ ": UNEXPECTED " ++ g2)

def report.go(label, want, gg):
  (g1, g2) = gg
  report.sel(label, g2, String.eq(g1, want))

def report(label, got, want):
  report.go(label, want, String.copy(got))

assert http_retry:
  forall port: U32
  forall r: Result<U32 & String, Listener>
  forall rest: IO(Listener & U32)
  IO(Listener & U32)

def http_retry(port, r, rest):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

assert http_bind:
  forall tries: Nat
  forall +port: +U32
  IO(Listener & U32)

def http_bind(tries, port):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free http port")
    case 1n+t:
      rest = http_bind(t, port + 1)
      do IO<Listener & U32>:
        r : Result<U32 & String, Listener> <- TCP.listen(port)
        http_retry(port, r, rest)

assert main_run:
  forall l: Listener
  forall +port: +U32
  IO(U32)

def main_run(l, port):
  wa = {"HTTP/1.1 200 OK\r\nContent-Length: 16\r\n\r\nHello from Bend!" : String}
  wb = {"HTTP/1.1 404 Not Found\r\nContent-Length: 9\r\n\r\nnot found" : String}
  do IO<U32>:
    a : Socket <- http_start(port, "GET / HTTP/1.1\r\nHost: 127.0.0.1\r\n\r\n")
    b : Socket <- http_start(port, "GET /nope HTTP/1.1\r\n\r\n")
    l2 : Listener <- http_serve(2n, l)
    ra : String <- http_finish(a)
    rb : String <- http_finish(b)
    u : Unit <- Listener.close(l2)
    v : Unit <- report("GET /", ra, wa)
    w : Unit <- report("GET /nope", rb, wb)
    return 0

assert main_go:
  forall b: Listener & U32
  IO(U32)

def main_go(b):
  (l, port) = b
  main_run(l, port)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    b : Listener & U32 <- http_bind(32n, 18080)
    main_go(b)
