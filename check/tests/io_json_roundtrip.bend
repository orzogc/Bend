# io pin (io_json_roundtrip): bend3's JSON module -- read/show
# roundtrip with escapes and nesting, located read errors, polite
# accessors defaulting on misses. bend4 has no JSON module -- rt dies
# first on the missing surface (List.get answers Maybe in bend4, so
# the accessor walk rides Maybe.default).
import Base

assert List.length:
  forall -A: Type
  forall xs: List<A>
  Nat

def List.length(A, xs):
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+List.length(A, t)

assert Nat.is_eq:
  forall a: Nat
  forall b: Nat
  Bool

def Nat.is_eq(a, b):
  Cmp.is_eq(Nat.cmp(a, b))

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

assert List.get:
  forall -A: Type
  forall n: Nat
  forall xs: List<A>
  Maybe<A>

def List.get(A, n, xs):
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n Con{h, t}:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{h, t}:
      List.get(A, p, t)

assert b2u:
  forall b: Bool
  U32

def b2u(b):
  if b: 1 else: 0

assert rt:
  forall s: String
  forall out: String
  U32

def rt(s, out):
  match JSON.read(s):
    case Done{j}:
      b2u(String.eq(JSON.show(j), out))
    case Fail{(p, m)}:
      0

assert bad:
  forall s: String
  forall at: U32
  U32

def bad(s, at):
  match JSON.read(s):
    case Done{j}:
      0
    case Fail{(p, m)}:
      b2u(U32.is_eq(p, at))

assert chk_access:
  U32

def chk_access():
  match JSON.read("{\"nums\": [10, 20, 30], \"name\": \"bend\"}"):
    case Done{v}:
      access_score(v)
    case Fail{(p, m)}:
      0

assert access_score:
  forall v: JSON
  U32

def access_score(v):
  n1 = Maybe.default(JSON, JSON.null(), List.get(JSON, 1n, JSON.items(JSON.get("nums", v))))
  a = b2u(U32.is_eq(JSON.as_u32(n1), 20))
  b = b2u(String.eq(JSON.as_string(JSON.get("name", v)), "bend"))
  c = b2u(Nat.is_eq(List.length(JSON, JSON.items(JSON.get("nums", v))), 3n))
  d = b2u(U32.is_eq(JSON.as_u32(JSON.get("missing", v)), 0))
  a + b + c + d

assert main:
  U32

def main():
  a = rt(" {\"a\" : [1, -2, \"x\\ny\", true, null], \"b\":{}, \"c\":[]} ", "{\"a\":[1,-2,\"x\\ny\",true,null],\"b\":{},\"c\":[]}")
  b = bad("[1,", 3)
  c = bad("", 0)
  d = chk_access()
  a * 1000 + b * 100 + c * 10 + d
$$ bend %
Error:
- expected : a defined name
- observed : JSON.read
Context:
- s   : String
- out : String
Location: rt
70 | def rt(s, out):
71>|   match JSON.read(s):
72 |     case Done{j}:
