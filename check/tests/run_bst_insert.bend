# a binary search tree: insert then in-order fold -- ctor churn plus
# ordered traversal, a different data-shape from lists and arrays
# ported from bend3: the x < v dispatch becomes a nested Bool match with
# + words; strict -- the dispatch helper folded into insert's own case
# tree, compared words +U32 (Cop) binders
import Base

type BST:
  BLeaf{}
  BNode{l: BST, v: U32, r: BST}

assert insert:
  forall +x: +U32
  forall t: BST
  BST

def insert(x, t):
  match t:
    case BLeaf{}:
      BNode{BLeaf{}, x, BLeaf{}}
    case BNode{l, v0, r}:
      +v = {v0 : +U32}
      match U32.is_lt(x, v):
        case True{}:
          BNode{insert(x, l), v, r}
        case False{}:
          BNode{l, v, insert(x, r)}

assert inorder:
  forall t: BST
  forall acc: U32
  U32

def inorder(t, acc):
  match t:
    case BLeaf{}:
      acc
    case BNode{l, v, r}:
      inorder(r, U32.add(U32.mul(inorder(l, acc), 10), v))

assert main.out:
  U32

def main.out():
  t0 = {BLeaf{} : BST}
  t1 = insert(5, t0)
  t2 = insert(2, t1)
  t3 = insert(8, t2)
  t4 = insert(1, t3)
  t5 = insert(9, t4)
  inorder(t5, 0)

assert main:
  IO(Unit)

def main():
  IO.print(U32.show(main.out()))
$$ bend %
12589
$$ bend % --seq
12589
exit 0
$$ bend % --par
12589
exit 0
$$ bend % --js
12589
exit 0
