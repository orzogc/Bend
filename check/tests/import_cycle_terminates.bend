# bend3 loaded a cyclic file pair as one book; bend4 REFUSES cycles by
# design (book_load's acyclic-graph law) -- the cycle itself needs a
# second file the single-file corpus cannot hold, so the pinned half
# is the eager leading-line load dying on its target
import Base
import /cycle/other_half.bend as C

assert main:
  U32

def main():
  0
$$ bend %
Error: ENOENT: no such file or directory, lstat '/cycle/other_half.bend'
