# bend3's ../../ module ascent reached C-bodied defs; bend4 has
# neither (imports open literal paths, C bodies are gone) -- the
# ascent's target dies at the leading line
import Base
import /up/up/native_mod.c as M

assert main:
  U32

def main():
  0
$$ bend %
Error: ENOENT: no such file or directory, lstat '/up/up/native_mod.c'
