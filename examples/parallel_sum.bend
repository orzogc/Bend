# A very simple example of a massively parallel program
# Creates a tree with numbers and then sums all values in parallel

# a binary tree
type MyTree(t):
  Node { val: t, ~left: MyTree(t), ~right: MyTree(t) }
  Leaf

# sums all values in a tree
def sum(tree: MyTree(u24)) -> u24:
  fold tree:
    case MyTree/Node:
      return tree.val + tree.left + tree.right
    case MyTree/Leaf:
      return 0

# generates a binary tree of given depth
def gen(depth: u24) -> MyTree(u24):
  bend height=0, val = 1:
    when height < depth:
      tree = MyTree/Node { val: val, left: fork(height+1, 2*val), right: fork(height+1, 2*val+1) }
    else:
      tree = MyTree/Leaf
  return tree

# returns the sum of [1 .. 2^16), truncated to 24 bits
def main() -> u24:
  return sum(gen(16))