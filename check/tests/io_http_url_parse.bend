# io pin (io_http_url_parse): bend3's read_url -- scheme dispatch
# (http/https, others Fail), default and explicit ports, default and
# query-carrying paths. bend4 has no HTTP library -- url_score dies
# first on the missing surface (a Url respells as its secure & host &
# port & path tuple; secure rides Bool).
import Base

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  if b: 1 else: 0

assert url_score:
  forall url: Bool & String & U32 & String
  forall sec: Bool
  forall h: String
  forall pt: U32
  forall pa: String
  U32

def url_score(url, sec, h, pt, pa):
  (secure, host, port, path) = url
  b2u(Cmp.is_eq(Bool.cmp(secure, sec))) + b2u(String.eq(host, h)) + b2u(U32.is_eq(port, pt)) + b2u(String.eq(path, pa))

assert chk_https:
  forall u: Result<U32 & String, Bool & String & U32 & String>
  U32

def chk_https(u):
  match u:
    case Done{url}:
      url_score(url, True{}, "example.com", 443, "/")
    case Fail{(c, e)}:
      0

assert chk_http:
  forall u: Result<U32 & String, Bool & String & U32 & String>
  U32

def chk_http(u):
  match u:
    case Done{url}:
      url_score(url, False{}, "localhost", 8080, "/echo?q=1")
    case Fail{(c, e)}:
      0

assert chk_bad:
  forall u: Result<U32 & String, Bool & String & U32 & String>
  U32

def chk_bad(u):
  match u:
    case Done{url}:
      0
    case Fail{(c, e)}:
      b2u(U32.is_eq(c, 400))

assert main:
  U32

def main():
  a = chk_https(HTTP.read_url("https://example.com/"))
  b = chk_http(HTTP.read_url("http://localhost:8080/echo?q=1"))
  c = chk_bad(HTTP.read_url("ftp://x/"))
  a * 100 + b * 10 + c
$$ bend %
Error:
- expected : a defined name
- observed : HTTP.read_url
Location: main
63 | def main():
64>|   a = chk_https(HTTP.read_url("https://example.com/"))
65 |   b = chk_http(HTTP.read_url("http://localhost:8080/echo?q=1"))
