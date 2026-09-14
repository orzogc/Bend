# The proofs of the HTTP server laws. The response is one closed
# string, so each proof names its witness (the part of the text the
# law leaves open) and closes by evaluation.
import Base
import ./main.bend as Srv
import ./LAWS.bend as Laws

def Laws.status_ok():
  ("Content-Type: text/html\r\nConnection: close\r\nContent-Length: 22\r\n\r\n<h1>Hello, world!</h1>", {==})

def Laws.page_after_headers():
  ("HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nConnection: close\r\n", {==})

def Laws.content_length():
  {==}
