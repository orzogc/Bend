# io (io_get_env_own): get_env reads the environment's OWN keys
# only, so "toString" is unset. The JS lookup once reached through
# process.env's prototype and answered Object.prototype.toString, a
# function no marshal can carry.
import Base

assert report:
  forall tag: String
  forall r: Result<U32 & String, String>
  IO(Unit)

def report(tag, r):
  match r:
    case Done{value}:
      IO.print(String.append(tag, "=set"))
    case Fail{error}:
      (code, message) = error
      IO.print(String.append(tag, "=unset"))

assert main:
  IO(U32)

def main():
  do IO<U32>:
    a : Result<U32 & String, String> <- IO.get_env("toString")
    x : Unit <- report("toString", a)
    b : Result<U32 & String, String> <- IO.get_env("hasOwnProperty")
    y : Unit <- report("hasOwnProperty", b)
    return 0
$$ bend %
toString=unset
hasOwnProperty=unset
$$ bend % --seq
toString=unset
hasOwnProperty=unset
exit 0
$$ bend % --par
toString=unset
hasOwnProperty=unset
exit 0
$$ bend % --js
toString=unset
hasOwnProperty=unset
exit 0
