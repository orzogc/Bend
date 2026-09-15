# The laws of the HTTP server. They pin http_response, the pure part
# of the program, for EVERY page: the response is a head, a blank
# line, then the page; a client that cuts at the first blank line
# reads the page back; and the response determines the page. A
# closed law pins the exact bytes on the wire for the demo's page.
# PROOF.bend must prove them.
import Base
import ./main.bend as Srv

# LAW: the response of any page is some head, then the blank line,
# then the page.
law page_after_blank:
  for +page: String
  exs head: String
  {head ++ ("\r\n\r\n" ++ page) == Srv.http_response(page) : String}

# LAW: a client that reads the text after the first blank line gets
# the page back, whatever the page holds.
law body_is_page:
  for +page: String
  {Srv.http_body(Srv.http_response(page)) == page : String}

# LAW: the response determines the page: two equal responses come
# from equal pages.
law response_inj:
  for +a: String
  for +b: String
  for  e: {Srv.http_response(a) == Srv.http_response(b) : String}
  {a == b : String}

# LAW: the bytes on the wire for the demo's page: the status line, the
# headers with Content-Length 22, the blank line, the page (closed, by
# evaluation).
law wire_bytes:
  {Srv.http_response(Srv.http_page()) == "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nConnection: close\r\nContent-Length: 22\r\n\r\n<h1>Hello, world!</h1>" : String}
