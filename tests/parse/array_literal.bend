# [x : T * n] is Array.new(T, n, x): a 2^n-slot array of x; the ": T"
# names the operators inside x, as the parens' ": T" does
import Base

def main() -> (Array<U32> & Array<Bool>):
  ([1 + 2 : U32 * 2n], [True{} : Bool * 1n])

#|Tuple{ANode{ANode{ALeaf{3}, ALeaf{3}}, ANode{ALeaf{3}, ALeaf{3}}}, ANode{ALeaf{True{}}, ALeaf{True{}}}}
