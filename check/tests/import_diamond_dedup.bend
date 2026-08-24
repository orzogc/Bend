# bend3 loaded a diamond once per module identity; bend4 dedups by
# realpath (Base imported twice below is one load) and the flat corpus
# cannot spell the tree -- the absent diamond top dies at its line
import Base
import Base
import /diamond/top.bend as D

assert main:
  U32

def main():
  0
$$ bend %
Error: ENOENT: no such file or directory, lstat '/diamond/top.bend'
