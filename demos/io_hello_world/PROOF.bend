# The proofs of the hello world laws. Each law is about one closed
# string, so each proof gives its witness and closes by evaluation.
import Base
import ./main.bend as Hello
import ./LAWS.bend as Laws

def Laws.greeting_text():
  {==}

def Laws.greeting_head():
  ("ello, world!", {==})

def Laws.greeting_last():
  ("Hello, world", {==})
