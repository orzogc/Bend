# io (io_request_out_of_band): a REQUEST never decodes outside the
# event loop, and a REAL IO.OP still does. Pure code may apply a
# foreign effect (IO(A) is a transparent function type) and match
# over the IO.OP it answers; a request reaching such a match is a
# refusal in EVERY lane, while an Emit built purely (here IO.pure's
# answer, decoded to "3" before the do block) passes the same guard
# and decodes. Before this pin the C lane decoded the request as the
# LAST constructor -- this program printed a bare newline (the kont
# closure read as a Halt message) and exited 0, silent wrong output
# against the other lanes -- while the compiled JS threw the request
# to the loop, which ran the effect and resumed its captured
# continuation, printing SECRET. That resume law has no C spelling:
# the loop only runs an effect after the pure evaluator answers (one
# heap owner at a time), and a device thread mid-kernel can never
# reach the loop, so the one shared law is the loud refusal. Now the
# C dispatch guards IO.OP matches (an aux past CID_HALT is a
# request; ERR_TAGS, fail-stop) and the JS loop's catch answers the
# fail-stop Halt line instead of running the effect: the effect
# never fires, nothing prints SECRET, and every lane refuses after
# printing "3". `bend run` executes the same compiled text as --js,
# one line and exit 1.
import Base

assert intercept:
  IO(U32)

def intercept():
  op = IO.print("SECRET")(U32, x => Emit{7})
  match op:
    case Emit{v}:
      do IO<U32>:
        u : Unit <- IO.print("emitted")
        return v
    case Halt{c, m}:
      do IO<U32>:
        u : Unit <- IO.print(m)
        return c

assert decode:
  forall op: IO.OP<U32>
  String

def decode(op):
  match op:
    case Emit{v}: U32.show(v)
    case Halt{c, m}: m

assert main:
  IO(U32)

def main():
  s = decode(IO.pure(U32, 3)(U32, x => Emit{x}))
  do IO<U32>:
    u : Unit <- IO.print(s)
    r : U32 <- intercept()
    return r
$$ bend %
3
bend: a request decoded outside the event loop
$$ bend % --js
3
bend: a request decoded outside the event loop
exit 1
$$ bend % --seq
3
bend: error 3: runtime fail-stop
signal SIGABRT
$$ bend % --par
3
bend: error 3: runtime fail-stop
signal SIGABRT
