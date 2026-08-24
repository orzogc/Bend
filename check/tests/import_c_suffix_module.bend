# bend3 resolved ./lib/helper.c to helper.c.bend; bend4 opens the
# import path LITERALLY -- the error names the unrewritten spelling
# (an absolute path keeps the golden stable: the corpus is single-file
# and no fixture tree exists)
import Base
import /lib/helper.c as H

assert main:
  U32

def main():
  0
$$ bend %
Error: ENOENT: no such file or directory, lstat '/lib/helper.c'
