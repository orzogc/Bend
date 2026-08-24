# bend3 canonicalized relative spellings to one module identity;
# bend4 dedups by realpath, which a flat corpus cannot exercise with
# two spellings of a real file -- the canonical target dies loudly
import Base
import /mods/canonical.bend as C

assert main:
  U32

def main():
  0
$$ bend %
Error: ENOENT: no such file or directory, lstat '/mods/canonical.bend'
