# bend3's bare re-exporting module tree carried one IO across files;
# bend4 imports are aliased single files, the corpus is flat, and no
# IO driver exists -- the leading-line load dies on the absent tree
import Base
import /shared/io_tree.bend as T

assert main:
  U32

def main():
  0
$$ bend %
Error: ENOENT: no such file or directory, lstat '/shared/io_tree.bend'
