# io (io_get_env): the environment surface: get_env answers Result --
# Done for a set variable, Fail (ENOENT) for an unset one. HOME's
# value is machine-local, so the test prints only which branch
# answered, matching on the Result instead of IO.try-ing it.
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
    a : Result<U32 & String, String> <- IO.get_env("HOME")
    x : Unit <- report("HOME", a)
    b : Result<U32 & String, String> <- IO.get_env("BEND_TEST_NO_SUCH_VAR_09AF")
    y : Unit <- report("BEND_TEST_NO_SUCH_VAR_09AF", b)
    return 0
$$ bend %
HOME=set
BEND_TEST_NO_SUCH_VAR_09AF=unset
$$ bend % --seq
HOME=set
BEND_TEST_NO_SUCH_VAR_09AF=unset
exit 0
$$ bend % --par
HOME=set
BEND_TEST_NO_SUCH_VAR_09AF=unset
exit 0
$$ bend % --js
HOME=set
BEND_TEST_NO_SUCH_VAR_09AF=unset
exit 0
