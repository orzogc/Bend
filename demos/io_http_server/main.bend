# HTTP server: a minimal HTTP/1.1 server in Bend over the TCP effect
# kit. It binds port 8080 and answers every connection with a hello
# world page: accept, then a spawned computation reads the request,
# sends the response and closes, so a slow client never holds the
# next one. The accept loop recurses on itself forever, so its def is
# @unsafe: the termination checker skips it, and the server runs
# until killed. The response is BUILT from the page: http_response
# puts the status line, the headers, a Content-Length header with the
# page's length in decimal, a blank line, and then the page. The Spec
# section holds what the laws talk about: a string's length, a prefix
# test by character codes, drop and take, and http_body, the cut a
# client makes to read the page back (the text after the first blank
# line). Handles are affine: every op threads its handle back OUTSIDE
# the Result, and each tuple destructures in its own helper. Try it:
#
#   bend demos/io_http_server/main.bend -o http_server && ./http_server
#   curl http://127.0.0.1:8080
import Base

# Spec
# ----

# the number of characters of a string
def length(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{h, t}:
      1n+length(t)

# the blank line that ends the headers
def sep() -> String:
  "\r\n\r\n"

# two characters have the same code
def char_eq(a: Char, b: Char) -> Bool:
  match a b:
    case Chr{x} Chr{y}:
      U32.is_eq(x, y)

# p is a prefix of s
def is_prefix(p: String, s: String) -> Bool:
  match p s:
    case SNil{} s2:
      True{}
    case SCon{a, pt} SNil{}:
      False{}
    case SCon{a, pt} SCon{b, st}:
      Bool.and(char_eq(a, b), is_prefix(pt, st))

# the text after its first n characters
def drop(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          drop(p, t)

# the cut a client makes: the text after the first blank line; e says
# whether the blank line starts at the current position
def http_body.go(s: String, e: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, +t}:
      match e:
        case True{}:
          drop(3n, t)
        case False{}:
          http_body.go(t, is_prefix(sep(), t))

def http_body(+s: String) -> String:
  http_body.go(s, is_prefix(sep(), s))

# Program
# -------

def http_page() -> String:
  "<h1>Hello, world!</h1>"

# the character of a decimal digit
def digit(d: Nat) -> Char:
  match d:
    case 0n:
      '0'
    case 1n:
      '1'
    case 2n:
      '2'
    case 3n:
      '3'
    case 4n:
      '4'
    case 5n:
      '5'
    case 6n:
      '6'
    case 7n:
      '7'
    case 8n:
      '8'
    case 9n:
      '9'
    case 10n+p:
      '0'

# one more on a little-endian digit list: a 9 becomes 0 and carries
def inc(ds: List<Nat>) -> List<Nat>:
  match ds:
    case []:
      [1n]
    case d <> t:
      match d:
        case 9n:
          0n <> inc(t)
        case q:
          (1n+q) <> t

# the decimal digits of a number, least significant first
def to_dec(n: Nat) -> List<Nat>:
  match n:
    case 0n:
      [0n]
    case 1n+p:
      inc(to_dec(p))

def rev.go(ds: List<Nat>, acc: List<Nat>) -> List<Nat>:
  match ds:
    case []:
      acc
    case d <> t:
      rev.go(t, d <> acc)

def rev(ds: List<Nat>) -> List<Nat>:
  rev.go(ds, [])

# the text of a digit list
def render(ds: List<Nat>) -> String:
  match ds:
    case []:
      SNil{}
    case d <> t:
      SCon{digit(d), render(t)}

# a number in decimal
def decimal(n: Nat) -> String:
  render(rev(to_dec(n)))

# the status line and the headers, up to the Content-Length value
def http_status() -> String:
  "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nConnection: close\r\nContent-Length: "

# the head of a response for a page of n characters
def http_head(n: Nat) -> String:
  http_status() ++ (decimal(n) ++ "\r\n\r\n")

# the response for a page: its head, then the page
def http_response(+page: String) -> String:
  http_head(length(page)) ++ page

law http_sent:
  for sent: Socket & Result<&1, &1, U32 & String, Unit>
  IO(Unit)

def http_sent(sent):
  (s, r) = sent
  do IO<Unit>:
    ok : Unit <- IO.pass(Unit, r)
    Socket.close(s)

law http_reply:
  for read: Socket & Result<&1, &1, U32 & String, String>
  IO(Unit)

def http_reply(read):
  (s, r) = read
  do IO<Unit>:
    req  : String <- IO.pass(String, r)
    sent : Socket & Result<&1, &1, U32 & String, Unit> <-
      TCP.send(s, http_response(http_page()))
    http_sent(sent)

law http_talk:
  for s: Socket
  IO(Unit)

def http_talk(s):
  do IO<Unit>:
    read : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 8192)
    http_reply(read)

law http_conn:
  for conn: Listener & Result<&1, &1, U32 & String, Socket>
  IO(Listener)

def http_conn(conn):
  (l, r) = conn
  do IO<Listener>:
    s  : Socket <- IO.pass(Socket, r)
    ok : Unit <- IO.spawn(Unit, http_talk(s))
    return l

law http_serve:
  for l: Listener
  IO(Unit)

@unsafe
def http_serve(l):
  do IO<Unit>:
    conn : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    next : Listener <- http_conn(conn)
    http_serve(next)

law main:
  IO(U32)

def main():
  do IO<U32>:
    l  : Listener <- IO.try(Listener, TCP.listen(8080))
    ok : Unit <- IO.print("serving http://127.0.0.1:8080")
    up : Unit <- http_serve(l)
    return 0
