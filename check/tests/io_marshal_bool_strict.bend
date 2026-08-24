# io (io_marshal_bool_strict): the seam has ONE value model -- the
# interpreter runs the compiled JS itself, so an effect's answer is
# whatever the .js body returns, trusted inbound in every lane. This
# golden pinned the dead two-model refusal ('a boolean Bool answer'):
# the interpreter marshaled answers by type and refused a 1 where
# compiled JS ran it. Now both lanes run the SAME text: flop's real
# boolean rides the honest round trip, loose answers 1 at Bool, and
# the Bool match runs it as truthy -- both lanes print "wide"
# byte-identically, which is the law this golden now guards.
import Base

assert flop:
  forall b: Bool
  IO(Bool)

def flop(b):
  import "./io_marshal_bool_strict.js"

assert loose:
  forall c: Bool
  IO(Bool)

def loose(c):
  import "./io_marshal_bool_strict.js"

assert main:
  IO(Unit)

def main():
  do IO<Unit>:
    b : Bool <- flop(True{})
    c : Bool <- loose(b)
    IO.print(if c: "wide" else: "open")
$$ bend %
wide
$$ bend % --js
wide
exit 0
