# bend3 chained a proof transitively over bare imports; bend4's flat
# corpus has no module tree to chain across -- the leading-line load
# dies on the absent file
import Base
import /shared/proof_chain.bend as P

assert main:
  U32

def main():
  0
$$ bend %
Error: ENOENT: no such file or directory, lstat '/shared/proof_chain.bend'
