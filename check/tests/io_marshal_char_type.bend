# io (io_marshal_char_type): a Char and a String are both JS strings,
# told apart only by type -- and with one value model nothing needs
# telling: an answered Char IS the string the continuation matches
# on, directly (getc), inside a ctor field (Maybe<Char>), and through
# a dependent Sigma pair (Char & String). Both lanes run the same
# compiled text and print the same three lines byte-identically.
import Base

assert getc:
  IO(Char)

def getc():
  import "./io_marshal_char_type.js"

assert pick:
  IO(Maybe<Char>)

def pick():
  import "./io_marshal_char_type.js"

assert stamp:
  IO(Char & String)

def stamp():
  import "./io_marshal_char_type.js"

assert code_of:
  forall m: Maybe<Char>
  U32

def code_of(m):
  match m:
    case None{}:
      0
    case Some{c}:
      match c:
        case Chr{n}:
          n

assert pair_show:
  forall p: Char & String
  String

def pair_show(p):
  match p:
    case Tuple{c, s}:
      String.append(U32.show(code_of(Some{c})), s)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    c : Char <- getc()
    t : Unit <- IO.print(U32.show(code_of(Some{c})))
    m : Maybe<Char> <- pick()
    u : Unit <- IO.print(U32.show(code_of(m)))
    p : Char & String <- stamp()
    v : Unit <- IO.print(pair_show(p))
    return 0
$$ bend %
65
90
113ok
$$ bend % --js
65
90
113ok
exit 0
