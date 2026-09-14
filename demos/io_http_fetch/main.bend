# HTTP client: a minimal HTTP/1.1 request in Bend over the TCP effect
# kit. It calls ip-api.com's public geolocation API and prints the
# answer: plain text lines with the status, country, city and IP of
# the caller. The effect kit speaks IPv4 quads (no DNS), so the demo
# connects to the API's address 208.95.112.1 and names the host in
# the Host header. The response is read in two sequential recvs:
# Connection close makes the second read the tail or an empty EOF.
# http_body strips the status line and headers: a rolling 4-byte
# window walks the bytes until it equals "\r\n\r\n" as a big-endian
# word (218762506), and answers the rest. Handles are affine: every
# op threads its handle back OUTSIDE the Result, and each tuple
# destructures in its own helper. Try it:
#
#   bend demos/io_http_fetch/main.bend
import Base

law http_body.go:
  for s: String
  for e: Bool
  for w: U32
  String

def http_body.go(s, e, w):
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{a}, t}:
      match e:
        case True{}:
          SCon{Chr{a}, t}
        case False{}:
          +w2 = (w * 256 + a : U32)
          http_body.go(t, U32.is_eq(w2, 218762506), w2)

law http_body:
  for s: String
  String

def http_body(s):
  http_body.go(s, False{}, 0)

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
