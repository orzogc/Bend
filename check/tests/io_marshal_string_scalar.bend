# io (io_marshal_string_scalar): the seam has ONE value model -- a
# String is the effect's JS string, walked by string_head/string_tail
# code point by code point in every lane. This golden pinned the dead
# two-model refusal ('a Unicode scalar Char code' on an ANSWER): the
# interpreter refused a lone surrogate half where compiled JS kept
# it, and two halves appended once counted 2 interpreted and 1
# compiled. With one model that divergence class cannot exist; the
# law is observable: the boundary scalars (55295, 57344, 1114111)
# cross as one-Char strings, a Char answer's code reads back exact,
# and a lone surrogate rides raw as its own code point -- torn
# ("a" then D800) counts 2 in both lanes, byte-identically.
import Base

assert low:
  IO(String)

def low():
  import "./io_marshal_string_scalar.js"

assert high:
  IO(String)

def high():
  import "./io_marshal_string_scalar.js"

assert apex:
  IO(String)

def apex():
  import "./io_marshal_string_scalar.js"

assert edge:
  IO(Char)

def edge():
  import "./io_marshal_string_scalar.js"

assert torn:
  IO(String)

def torn():
  import "./io_marshal_string_scalar.js"

assert count:
  forall s: String
  U32

def count(s):
  match s:
    case SNil{}:
      0
    case SCon{h, t}:
      U32.add(1, count(t))

assert code_of:
  forall c: Char
  U32

def code_of(c):
  match c:
    case Chr{n}:
      n

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : String <- low()
    b : String <- high()
    c : String <- apex()
    d : Char <- edge()
    e : String <- torn()
    u : Unit <- IO.print(U32.show(count(a)))
    v : Unit <- IO.print(U32.show(count(b)))
    w : Unit <- IO.print(U32.show(count(c)))
    x : Unit <- IO.print(U32.show(code_of(d)))
    y : Unit <- IO.print(U32.show(count(e)))
    return 0
$$ bend %
1
1
1
55295
2
$$ bend % --js
1
1
1
55295
2
exit 0
