# io (io_nul_bytes): a NUL byte never crosses a char* OS seam. The
# C kit once NUL-truncated (io_cstr's terminator): path bytes
# "/tmp/x" 00 "y" opened the truncated name on disk, a mode "w" 00
# "x" passed strcmp, get_env of "PATH" 00 "X" answered PATH's own
# value, and a NUL host dialed the truncated quad -- while the JS
# lanes refused each (the path with fs's junk EIO 5). Every seam now
# refuses the NUL loud and identically in every lane: EILSEQ for a
# path, EINVAL for a mode or host, a plain miss for an env name.
import Base

assert nul_tail:
  String

def nul_tail():
  SCon{Chr{0}, SCon{Chr{88}, SNil{}}}

assert path_go:
  forall r: Result<U32 & String, File>
  IO(Unit)

def path_go(r):
  match r:
    case Done{file}:
      do IO<Unit>:
        x : Unit <- File.close(file)
        IO.print("path=opened")
    case Fail{error}:
      (code, message) = error
      do IO<Unit>:
        x : Unit <- IO.print(String.append("path=fail:", U32.show(code)))
        IO.print(message)

assert mode_go:
  forall r: Result<U32 & String, File>
  IO(Unit)

def mode_go(r):
  match r:
    case Done{file}:
      do IO<Unit>:
        x : Unit <- File.close(file)
        IO.print("mode=opened")
    case Fail{error}:
      (code, message) = error
      IO.print(String.append("mode=fail:", U32.show(code)))

assert env_go:
  forall r: Result<U32 & String, String>
  IO(Unit)

def env_go(r):
  match r:
    case Done{value}:
      IO.print("env=hit")
    case Fail{error}:
      (code, message) = error
      IO.print(String.append("env=miss:", U32.show(code)))

assert host_go:
  forall r: Result<U32 & String, Socket>
  IO(Unit)

def host_go(r):
  match r:
    case Done{sock}:
      do IO<Unit>:
        x : Unit <- Socket.close(sock)
        IO.print("host=dialed")
    case Fail{error}:
      (code, message) = error
      IO.print(String.append("host=fail:", U32.show(code)))

assert main:
  IO(U32)

def main():
  do IO<U32>:
    r : Result<U32 & String, File> <- File.open(String.append("/tmp/bend_io_nul_", nul_tail()), "w")
    a : Unit <- path_go(r)
    m : Result<U32 & String, File> <- File.open("/tmp/bend_io_nul_mode", String.append("w", nul_tail()))
    b : Unit <- mode_go(m)
    e : Result<U32 & String, String> <- IO.get_env(String.append("PATH", nul_tail()))
    c : Unit <- env_go(e)
    s : Result<U32 & String, Socket> <- TCP.connect(String.append("127.0.0.1", nul_tail()), 1)
    d : Unit <- host_go(s)
    return 0
$$ bend %
path=fail:92
Illegal byte sequence
mode=fail:22
env=miss:2
host=fail:22
$$ bend % --seq
path=fail:92
Illegal byte sequence
mode=fail:22
env=miss:2
host=fail:22
exit 0
$$ bend % --par
path=fail:92
Illegal byte sequence
mode=fail:22
env=miss:2
host=fail:22
exit 0
$$ bend % --js
path=fail:92
Illegal byte sequence
mode=fail:22
env=miss:2
host=fail:22
exit 0
