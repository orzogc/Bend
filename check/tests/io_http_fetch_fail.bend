# io pin (io_http_fetch_fail): bend3's fetch died on DNS resolution of
# an RFC-2606 .invalid host and exited with the ENOENT class word (2),
# the Fail carried as a Result. bend4 has no HTTP library -- the do
# block dies on the missing HTTP.fetch.
import Base

assert die_on:
  forall r: Result<U32 & String, String>
  IO(U32)

def die_on(r):
  match r:
    case Done{resp}:
      IO.die(U32, 1, "unreached")
    case Fail{(code, error)}:
      IO.die(U32, code, error)

assert main:
  IO(U32)

def main():
  do IO<U32>:
    r : Result<U32 & String, String> <- HTTP.fetch("http://bend-test.invalid/")
    die_on(r)
$$ bend %
Error:
- expected : a defined name
- observed : HTTP.fetch
Location: main
22 |   do IO<U32>:
23>|     r : Result<U32 & String, String> <- HTTP.fetch("http://bend-test.invalid/")
24 |     die_on(r)
