# io (io_stale_handle_rank): the handle gate outranks the argument
# codecs, one rank in every backend. The kit's law everywhere is
# subject first: a dead handle answers Fail(EBADF) whatever the
# other arguments hold -- and udp_send_to is the one effect taking
# both a handle and a NUL-checked host, where the C wrapper's NUL
# refusal once jumped that gate: a stale socket with a NUL host
# answered EINVAL in C and EBADF in the JS lanes, and the C kit
# even split against itself (the same stale socket with a merely
# malformed host answered EBADF). The NUL check now sits behind the
# handle gate, so the rank is EBADF, then EINVAL, in every lane; a
# live handle with a NUL host still refuses EINVAL, never truncates.
import Base

law nul_host:
  String

def nul_host():
  SCon{Chr{0}, SNil{}}

law sent:
  for tag : String
  for m   : Socket & Result<&1, &1, (U32 & String), Unit>
  IO(Unit)

def sent(tag, m):
  (s, r) = m
  match r:
    case Done{value}:
      do IO<Unit>:
        p : Unit <- IO.print(String.append(tag, "=done"))
        Socket.close(s)
    case Fail{error}:
      (code, message) = error
      do IO<Unit>:
        p : Unit <- IO.print(String.append(tag, String.append("=fail:", U32.show(code))))
        q : Unit <- IO.print(message)
        Socket.close(s)

law stale_probe:
  for s: Socket
  IO(Unit)

def stale_probe(s):
  match s:
    case Socket{slot, gen}:
      +a = {slot : U32}
      +b = {gen : U32}
      do IO<Unit>:
        u : Unit <- Socket.close(Socket{a, b})
        m : Socket & Result<&1, &1, (U32 & String), Unit> <- UDP.send_to(Socket{a, b}, nul_host(), 9, "x")
        n : Unit <- sent("stale_nul", m)
        w : Socket & Result<&1, &1, (U32 & String), Unit> <- UDP.send_to(Socket{a, b}, "1.2.3.", 9, "x")
        sent("stale_bad", w)

law live_probe:
  for s: Socket
  IO(Unit)

def live_probe(s):
  do IO<Unit>:
    m : Socket & Result<&1, &1, (U32 & String), Unit> <- UDP.send_to(s, nul_host(), 9, "x")
    sent("live_nul", m)

law main:
  IO(U32)

def main():
  do IO<U32>:
    s : Socket <- IO.try(Socket, UDP.bind(0))
    u : Unit <- live_probe(s)
    t : Socket <- IO.try(Socket, UDP.bind(0))
    v : Unit <- stale_probe(t)
    return 0

#|live_nul=fail:22
#|Invalid argument
#|stale_nul=fail:9
#|Bad file descriptor
#|stale_bad=fail:9
#|Bad file descriptor
