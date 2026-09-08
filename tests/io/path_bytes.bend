# io (io_path_bytes): a path reaches the OS as BYTES, one byte per
# Char, in every lane -- the inbound twin of io_text_bytes' write
# law. file_open.js once handed fs.openSync the raw JS string, which
# UTF-8 encodes: path bytes C3 A9 opened "é" under C and a
# double-encoded "Ã©" under --js and the interpreter, and a lone E9
# -- invalid UTF-8, EILSEQ on APFS -- failed 92 under C yet opened a
# two-byte name in both JS lanes. The path now crosses as a Buffer
# of the Char codes, and get_env's name lookup decodes its key bytes
# the same way. The lone-byte probe pins the encoding: only a
# raw-byte path can answer EILSEQ.
import Base

law good:
  String

def good():
  String.append("/tmp/bend_io_path_", SCon{Chr{195}, SCon{Chr{169}, SNil{}}})

law lone:
  String

def lone():
  String.append("/tmp/bend_io_path_", SCon{Chr{233}, SNil{}})

law write_go:
  for w: File & Result<&1, &1, (U32 & String), Unit>
  IO(Unit)

def write_go(w):
  (f, r) = w
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

law read_go:
  for m: File & Result<&1, &1, (U32 & String), String>
  IO(U32)

def read_go(m):
  (f, r) = m
  do IO<U32>:
    data : String <- IO.pass(String, r)
    p    : Unit <- IO.print(data)
    x    : Unit <- File.close(f)
    return 0

law probe_lone:
  for r: Result<&1, &1, (U32 & String), File>
  IO(Unit)

def probe_lone(r):
  match r:
    case Done{file}:
      IO.print("lone-opened")
    case Fail{error}:
      (code, message) = error
      IO.print(message)

law main:
  IO(U32)

def main():
  do IO<U32>:
    f : File <- IO.try(File, File.open(good(), "w"))
    w : File & Result<&1, &1, (U32 & String), Unit> <- File.write(f, "bend-path")
    x : Unit <- write_go(w)
    r : Result<&1, &1, (U32 & String), File> <- File.open(lone(), "w")
    y : Unit <- probe_lone(r)
    g : File <- IO.try(File, File.open(good(), "r"))
    m : File & Result<&1, &1, (U32 & String), String> <- File.read(g, 64)
    read_go(m)

#|Illegal byte sequence
#|bend-path
