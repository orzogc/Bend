# io pin (io_http_request_roundtrip): bend3's HTTP pure layer --
# request/response head reading, serialization roundtrip, the
# case-insensitive header lookup and tolerant line handling. bend4 has
# no HTTP library -- req_score dies first on the missing get_header (a
# Request respells as its method & path & headers & length tuple).
import Base

assert Maybe.default:
  forall -A: Type
  forall m: Maybe<A>
  forall d: A
  A

def Maybe.default(A, m, d):
  match m:
    case None{}:
      d
    case Some{x}:
      x

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  if b: 1 else: 0

assert req_score:
  forall req: String & String & List<String & String> & U32
  U32

def req_score(req):
  (m, p, hs, b) = req
  b2u(String.eq(m, "GET")) + b2u(String.eq(p, "/a")) + b2u(String.eq(HTTP.get_header("", "Host", hs), "x")) + b2u(String.eq(HTTP.get_header("", "ACCEPT", hs), "*/*"))

assert chk_parse:
  U32

def chk_parse():
  match HTTP.read_request("GET /a HTTP/1.1\r\nhOsT: x\r\nAccept:  */*  \r\n"):
    case Done{req}:
      req_score(req)
    case Fail{(c, e)}:
      0

assert rt_score:
  forall req: String & String & List<String & String> & U32
  U32

def rt_score(req):
  (m, p, hs, b) = req
  b2u(String.eq(m, "POST")) + b2u(String.eq(p, "/echo")) + b2u(U32.is_eq(Maybe.default(U32, 0, U32.read(HTTP.get_header("", "content-length", hs))), 5))

assert chk_roundtrip:
  U32

def chk_roundtrip():
  match HTTP.read_request(HTTP.show_request("POST", "/echo", [("Host", "h")], 5)):
    case Done{req}:
      rt_score(req)
    case Fail{(c, e)}:
      0

assert chk_response:
  U32

def chk_response():
  match HTTP.read_response(HTTP.show_response(404, [], 0)):
    case Done{resp}:
      resp_status_is(resp, 404)
    case Fail{(c, e)}:
      0

assert resp_status_is:
  forall resp: U32 & List<String & String> & U32
  forall want: U32
  U32

def resp_status_is(resp, want):
  (s, hs, b) = resp
  b2u(U32.is_eq(s, want))

assert chk_bad:
  U32

def chk_bad():
  match HTTP.read_request("GARBAGE\r\n"):
    case Done{req}:
      0
    case Fail{(c, e)}:
      b2u(U32.is_eq(c, 400))

assert main:
  U32

def main():
  chk_parse() * 1000 + chk_roundtrip() * 100 + chk_response() * 10 + chk_bad()
$$ bend %
Error:
- expected : a defined name
- observed : HTTP.get_header
Context:
- m  : String
- p  : String
- hs : List<&_:String -> String>
- b  : U32
Location: req_score
33 |   (m, p, hs, b) = req
34>|   b2u(String.eq(m, "GET")) + b2u(String.eq(p, "/a")) + b2u(String.eq(HTTP.get_header("", "Host", hs), "x")) + b2u(String.eq(HTTP.get_header("", "ACCEPT", hs), "*/*"))
35 |
