# io pin (io_http_keep_alive): bend3's keep-alive pure layer -- the
# Connection/version decision, the stamped Connection header and
# read_head's version flag. bend4 has no HTTP library -- chk_keep dies
# first on the missing surface (a Header respells as a name & value
# tuple, a Response as its status & headers & body triple).
import Base

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  if b: 1 else: 0

assert chk_keep:
  U32

def chk_keep():
  a = b2u(HTTP.keep_alive(True{}, []))
  b = b2u(HTTP.keep_alive(True{}, [("Connection", "close")]))
  c = b2u(HTTP.keep_alive(False{}, []))
  d = b2u(HTTP.keep_alive(False{}, [("cOnNeCtIoN", " Keep-Alive ")]))
  a + b2u(U32.is_eq(b, 0)) + b2u(U32.is_eq(c, 0)) + d

assert conn_of:
  forall keep: Bool
  String

def conn_of(keep):
  (s, hs, bd) = HTTP.with_connection(keep, HTTP.ok("x"))
  HTTP.get_header("", "Connection", hs)

assert chk_stamp:
  U32

def chk_stamp():
  b2u(String.eq(conn_of(True{}), "keep-alive")) + b2u(String.eq(conn_of(False{}), "close"))

assert flag_of:
  forall text: String
  U32

def flag_of(text):
  match HTTP.read_head(text):
    case Done{h}:
      head_flag(h)
    case Fail{(cd, e)}:
      9

assert head_flag:
  forall h: Bool & (String & String & List<String & String> & U32)
  U32

def head_flag(h):
  (v, req) = h
  (m, p, hs, bd) = req
  b2u(v) * b2u(String.eq(m, "GET"))

assert chk_head:
  U32

def chk_head():
  b2u(U32.is_eq(flag_of("GET / HTTP/1.1\r\nHost: x\r\n"), 1)) + b2u(U32.is_eq(flag_of("GET / HTTP/1.0\r\nHost: x\r\n"), 0))

assert main:
  U32

def main():
  chk_keep() * 100 + chk_stamp() * 10 + chk_head()
$$ bend %
Error:
- expected : a defined name
- observed : HTTP.keep_alive
Location: chk_keep
18 | def chk_keep():
19>|   a = b2u(HTTP.keep_alive(True{}, []))
20 |   b = b2u(HTTP.keep_alive(True{}, [("Connection", "close")]))
