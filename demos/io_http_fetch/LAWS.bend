# The laws of the HTTP client. They pin http_body, the pure part of
# the program: the cut that strips the status line and the headers
# off a response, by a rolling 4-byte window that stops at the first
# blank line. PROOF.bend must prove them.
import Base
import ./main.bend as Fetch

# LAW: a response with a blank line after its headers gives the text
# after that blank line.
law body_after_headers:
  {Fetch.http_body("HTTP/1.1 200 OK\r\nHost: x\r\n\r\nbody") == "body" : String}

# LAW: a text with no blank line has no body.
law body_none:
  {Fetch.http_body("HTTP/1.1 200 OK\r\nHost: x\r\n") == "" : String}

# LAW: once the window has matched, the rest of the text is the body,
# whatever the window holds.
law body_rest:
  for s: String
  for w: U32
  {Fetch.http_body.go(s, True{}, w) == s : String}

# LAW: the body is a suffix of the text: some prefix, followed by the
# body, is the text itself.
law body_suffix:
  for s: String
  exs p: String
  {p ++ Fetch.http_body(s) == s : String}
