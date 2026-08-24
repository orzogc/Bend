# io pin (io_http_chunked_bytes): bend3's HTTP byte layer -- chunked
# decoding (hex sizes, extensions skipped) and the Bytes encode/decode
# roundtrip. bend4 has no HTTP library, and Bytes is ruled to a plain
# Array of U32 with no module -- the decode helper dies first on the
# missing surface (a Bytes value respells as its length & data pair).
import Base

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  if b: 1 else: 0

assert dec_eq:
  forall r: Result<U32 & String, List<U32>>
  forall out: String
  U32

def dec_eq(r, out):
  match r:
    case Done{bs}:
      b2u(String.eq(Bytes.decode(bs), out))
    case Fail{(c, e)}:
      0

assert dec_bad:
  forall r: Result<U32 & String, List<U32>>
  U32

def dec_bad(r):
  match r:
    case Done{bs}:
      0
    case Fail{(c, e)}:
      b2u(U32.is_eq(c, 400))

assert chk_chunked:
  U32

def chk_chunked():
  dec_eq(HTTP.unchunk(Bytes.encode("4\r\nWiki\r\n5;ext=1\r\npedia\r\n0\r\n\r\n")), "Wikipedia")

assert chk_chunked_bad:
  U32

def chk_chunked_bad():
  dec_bad(HTTP.unchunk(Bytes.encode("4\r\nWi")))

assert chk_pack:
  U32

def chk_pack():
  (n, data) = Bytes.from_string("héllo ✓")
  b2u(U32.is_eq(n, 10)) + b2u(String.eq(Bytes.decode(data), "héllo ✓"))

assert main:
  U32

def main():
  chk_chunked() * 100 + chk_chunked_bad() * 10 + chk_pack()
$$ bend %
Error:
- expected : a defined name
- observed : Bytes.decode
Context:
- bs  : List<U32>
- out : String
Location: dec_eq
22 |     case Done{bs}:
23>|       b2u(String.eq(Bytes.decode(bs), out))
24 |     case Fail{(c, e)}:
