# regression (AUDIT 1): a completed call's answer never refolds to the
# call -- the wnf once kept the def's exhausted equation active while
# entering the returned value, so a stuck match inside the result
# rebuilt as the finished call (id2(Type, M(b)) instead of M(b)) and a
# legal proof failed conversion. Both value doors are pinned: the
# forced-thunk result (id_delta) and a bound variable's value applied
# to an argument (ap_delta).
import Base

assert id2:
  forall -A: Type
  forall x: A
  A

def id2(A, x):
  x

assert id_delta:
  forall -b: Bool
  {id2(Type, (\{True: Type; False: Type})(b)) == (\{True: Type; False: Type})(b) : Type}

def id_delta(b):
  {==}

assert ap:
  forall -A: Type
  forall -B: Type
  forall f: @x: A -> B
  forall a: A
  B

def ap(A, B, f, a):
  f(a)

assert ap_delta:
  forall -b: Bool
  {ap(Bool, Type, (\{True: Type; False: Type}), b) == (\{True: Type; False: Type})(b) : Type}

def ap_delta(b):
  {==}

assert main:
  Bool

def main():
  True{}
$$ bend %
True{}
