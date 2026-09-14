# The laws of the HTTP server. They pin its pure part: the response
# text every connection gets (http_response) and the page inside it
# (http_page). PROOF.bend must prove them.
import Base
import ./main.bend as Srv

# LAW: the response is an HTTP/1.1 200 OK: it starts with that status
# line, and some rest follows.
law status_ok:
  exs rest: String
  {Srv.http_response() == "HTTP/1.1 200 OK\r\n" ++ rest : String}

# LAW: the response ends with the Content-Length header, the blank line
# that closes the headers, and then the page.
law page_after_headers:
  exs head: String
  {Srv.http_response() == head ++ "Content-Length: 22\r\n\r\n" ++ Srv.http_page() : String}

# LAW: the page has 22 characters, the count the Content-Length header
# declares.
law content_length:
  {Srv.http_length(Srv.http_page()) == 22n : Nat}
