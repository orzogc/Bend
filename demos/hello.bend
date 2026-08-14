# Self-contained hello world: declares the string surface it touches
# and a structural String.append. The JS backend wires String.append to
# the runtime's string_append by name; the evaluator runs the body. Both
# print the same string.

type Bool:
  False{}
  True{}

type Nat:
  Zero{}
  Succ{pred: Nat}

assert Word:
  forall n: Nat
  Type

type Word.Nil:
  WNil{}

type Word.Con<-p: Nat>:
  WCon{head: Bool, tail: Word(p)}

def Word(n):
  match n:
    case 0n:
      Word.Nil
    case 1n+p:
      Word.Con<p>

type U32:
  U32{data: Word(32n)}

type Char:
  Chr{code: U32}

type String:
  SNil{}
  SCon{head: Char, tail: String}

def String.append(a: String, b: String) -> String:
  match a:
    case SNil{}:
      b
    case SCon{h, t}:
      SCon{h, String.append(t, b)}

def main() -> String:
  String.append("Hello, ", "world!")
