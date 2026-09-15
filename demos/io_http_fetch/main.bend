# HTTP client: a minimal HTTP/1.1 request in Bend over the TCP effect
# kit. It calls ip-api.com's public geolocation API and prints the
# answer: plain text lines with the status, country, city and IP of
# the caller. The effect kit speaks IPv4 quads (no DNS), so the demo
# connects to the API's address 208.95.112.1 and names the host in
# the Host header. The response is read in two sequential recvs:
# Connection close makes the second read the tail or an empty EOF.
# http_body strips the status line and headers: it walks the text
# with a flag that says whether the blank line "\r\n\r\n" starts at
# the current position, and answers what follows the first blank
# line. The Spec section holds the notions the laws use: a prefix
# test by character codes, drop and take, and no_sep, the scan that
# says a text has no blank line. Handles are affine: every op threads
# its handle back OUTSIDE the Result, and each tuple destructures in
# its own helper. Try it:
#
#   bend demos/io_http_fetch/main.bend
import Base

# Spec
# ----

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

# the first n characters of a text
def take(n: Nat, s: String) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          SCon{h, take(p, t)}

# no position of the text starts a blank line; e says whether the
# current position does
def no_sep.go(s: String, e: Bool) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, +t}:
      match e:
        case True{}:
          False{}
        case False{}:
          no_sep.go(t, is_prefix(sep(), t))

def no_sep(+s: String) -> Bool:
  no_sep.go(s, is_prefix(sep(), s))

# Program
# -------

# the text after the first blank line; e says whether the blank line
# starts at the current position: then the body is the text after
# the 4 characters of the blank line
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

law fetch_tail:
  for head: String
  for rest: Socket & Result<&1, &1, U32 & String, String>
  IO(String)

def fetch_tail(head, rest):
  (s, r) = rest
  do IO<String>:
    tail : String <- IO.pass(String, r)
    ok   : Unit <- Socket.close(s)
    return head ++ tail

law fetch_head:
  for read: Socket & Result<&1, &1, U32 & String, String>
  IO(String)

def fetch_head(read):
  (s, r) = read
  do IO<String>:
    head : String <- IO.pass(String, r)
    rest : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 8192)
    fetch_tail(head, rest)

law fetch_sent:
  for sent: Socket & Result<&1, &1, U32 & String, Unit>
  IO(String)

def fetch_sent(sent):
  (s, r) = sent
  do IO<String>:
    ok   : Unit <- IO.pass(Unit, r)
    read : Socket & Result<&1, &1, U32 & String, String> <- TCP.recv(s, 8192)
    fetch_head(read)

law main:
  IO(U32)

def main():
  ra = {"GET /line/?fields=status,country,city,query HTTP/1.1\r\n" : String}
  rb = {"Host: ip-api.com\r\nConnection: close\r\n\r\n" : String}
  do IO<U32>:
    c    : Socket <- IO.try(Socket, TCP.connect("208.95.112.1", 80))
    sent : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send(c, ra ++ rb)
    resp : String <- fetch_sent(sent)
    ok   : Unit <- IO.print(http_body(resp))
    return 0
