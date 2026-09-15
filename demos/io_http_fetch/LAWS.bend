# The laws of the HTTP client. They pin http_body, the pure part of
# the program: the cut that strips the status line and the headers
# off a response, for EVERY text. The body is a suffix of the text;
# a text with no blank line has no body; and the text after a blank
# line is the body, whenever nothing before it looks like one.
# PROOF.bend must prove them. A Bool fact is stated with True{} on
# the left, the side a rewrite keeps.
import Base
import ./main.bend as Fetch

# LAW: the body is a suffix of the text: some prefix, followed by the
# body, is the text itself.
law body_suffix:
  for +s: String
  exs p: String
  {p ++ Fetch.http_body(s) == s : String}

# LAW: a text with no blank line has no body.
law body_none:
  for +s: String
  for e: {True{} == Fetch.no_sep(s) : Bool}
  {Fetch.http_body(s) == "" : String}

# LAW: headers, a blank line, then a body: the body is what http_body
# answers, whenever no blank line starts inside the headers or at
# their junction with the blank line (no_sep of the headers followed
# by "\r\n\r", the longest start of a blank line that ends before it).
law body_after_headers:
  for  h: String
  for +b: String
  for  e: {True{} == Fetch.no_sep(h ++ "\r\n\r") : Bool}
  {Fetch.http_body(h ++ ("\r\n\r\n" ++ b)) == b : String}

# LAW: a response with a blank line after its headers gives the text
# after that blank line (closed, by evaluation).
law body_example:
  {Fetch.http_body("HTTP/1.1 200 OK\r\nHost: x\r\n\r\nbody") == "body" : String}
