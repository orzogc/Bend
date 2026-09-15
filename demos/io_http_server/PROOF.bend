# The proofs of the HTTP server laws. http_response(page) unfolds to
# the closed characters of http_status(), then the decimal digits of
# the page's length (an opaque digit list, rendered by render), then
# the blank line, then the page.
#
# page_after_blank: the head is the status text and the digits; the
# proof re-associates the appends (app_assoc, an induction).
# body_is_page: the client's walker passes the status text by
# evaluation, and the digits by through_digits: an induction over the
# digit list, where every digit character differs from '\r'
# (digit_not_cr, a case analysis over the digit), so the flag stays
# clear; the blank line then sets the flag, and drop(3) answers the
# page.
# response_inj: cut both responses at the blank line (body_is_page)
# and the pages are equal.
import Base
import ./main.bend as Srv
import ./LAWS.bend as Laws

# Head, blank line, page
# ----------------------

def app_assoc(a: String, -b: String, -c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %app_assoc(t, b, c) : {SCon{h, (t ++ b) ++ c} == SCon{h, _} : String}
      {==}

def page_after_blank.pf(+page: String) -> {(Srv.http_status() ++ Srv.decimal(Srv.length(page))) ++ ("\r\n\r\n" ++ page) == Srv.http_response(page) : String}:
  %app_assoc(Srv.decimal(Srv.length(page)), "\r\n\r\n", page) : {Srv.http_status() ++ _ == Srv.http_response(page) : String}
  {==}

def Laws.page_after_blank(page):
  (Srv.http_status() ++ Srv.decimal(Srv.length(page)), page_after_blank.pf(page))

# The client reads the page
# -------------------------

# no digit character is '\r'
def digit_not_cr(d: Nat) -> {False{} == Srv.char_eq(Chr{13}, Srv.digit(d)) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      {==}

# the walker passes any rendered digit list with its flag clear
def through_digits(ds: List<Nat>, +rest: String)
  -> {Srv.http_body.go(rest, Srv.is_prefix(Srv.sep(), rest)) == Srv.http_body.go(Srv.render(ds) ++ rest, Srv.is_prefix(Srv.sep(), Srv.render(ds) ++ rest)) : String}:
  match ds:
    case []:
      {==}
    case +d <> t:
      %digit_not_cr(d) : {Srv.http_body.go(rest, Srv.is_prefix(Srv.sep(), rest)) == Srv.http_body.go(SCon{Srv.digit(d), Srv.render(t) ++ rest}, Bool.and(_, Srv.is_prefix("\n\r\n", Srv.render(t) ++ rest))) : String}
      through_digits(t, rest)

def Laws.body_is_page(page):
  %page_after_blank.pf(page) : {Srv.http_body(_) == page : String}
  %through_digits(Srv.rev(Srv.to_dec(Srv.length(page))), "\r\n\r\n" ++ page) : {_ == page : String}
  {==}

# The response determines the page
# --------------------------------

def Laws.response_inj(a, b, e):
  %Laws.body_is_page(a) : {_ == b : String}
  %Laws.body_is_page(b) : {Srv.http_body(Srv.http_response(a)) == _ : String}
  Equal.cong(String, String, s => Srv.http_body(s), Srv.http_response(a), Srv.http_response(b), e)

def Laws.wire_bytes():
  {==}
