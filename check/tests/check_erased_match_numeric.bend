# bend3's pin that erased numeric switching cannot inspect its
# argument. bend4 spells the erased arrow as a - binder, and has no
# numeric match-lambda at all: the \{0: ...} key dies at parse before
# erasure is even a question
import Base

assert hidden:
  @-x:U32 -> U32

def hidden():
  \{0: 0; (1)}

assert main:
  U32

def main():
  hidden(5)
$$ bend %
Error:
- expected : '}'
- observed : ':'
Location:
10 | def hidden():
11>|   \{0: 0; (1)}
12 |
