# The proofs of the HTTP client laws. http_body(s) is the walker
# http_body.go at the state is_prefix(sep, s), so each proof is an
# induction over the text at every state of the walker.
#
# body_suffix (suffix_go): when the flag is set, the body is drop(3)
# of the rest, and take(3) of it is the prefix (take_drop); when it is
# clear, the prefix grows by the character consumed, and the induction
# hypothesis gives the rest.
# body_none (none_go): a set flag contradicts no_sep; a clear flag
# steps both walkers together.
# body_after_headers: an induction on the headers. The flag at a
# header character only looks 4 characters ahead, so it is the same
# in front of "\r\n\r" and in front of "\r\n\r\n" ++ b (agree, a case
# analysis 3 characters deep). no_sep of the headers then says that
# flag is clear (step, deciding it with the Bool-inspect idiom), and
# both walkers advance to the induction hypothesis. At the end of the
# headers the flag is set by evaluation and drop(3) answers b.
import Base
import ./main.bend as Fetch
import ./LAWS.bend as Laws

# BD(b, t, f) picks a type by a Bool, so a rewrite through it refutes
# a clash between True{} and False{}
def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

# Suffix
# ------

# take(n) and drop(n) split a text
def take_drop(n: Nat, s: String) -> {Fetch.take(n, s) ++ Fetch.drop(n, s) == s : String}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match s:
        case SNil{}:
          {==}
        case SCon{h, t}:
          %take_drop(p, t) : {SCon{h, Fetch.take(p, t) ++ Fetch.drop(p, t)} == SCon{h, _} : String}
          {==}

# the prefix grows by the character the walker consumed
def suffix_step(+h: Char, -t: String, -e: Bool, ih: (&p: String -> {p ++ Fetch.http_body.go(t, e) == t : String}))
  -> (&p: String -> {p ++ Fetch.http_body.go(t, e) == SCon{h, t} : String}):
  (p, pf) = ih
  (SCon{h, p}, Equal.cong(String, String, x => SCon{h, x}, p ++ Fetch.http_body.go(t, e), t, pf))

# the suffix law over the walker, at every state
def suffix_go(s: String, e: Bool) -> (&p: String -> {p ++ Fetch.http_body.go(s, e) == s : String}):
  match s:
    case SNil{}:
      ("", {==})
    case SCon{+h, +t}:
      match e:
        case True{}:
          (SCon{h, Fetch.take(3n, t)}, Equal.cong(String, String, x => SCon{h, x}, Fetch.take(3n, t) ++ Fetch.drop(3n, t), t, take_drop(3n, t)))
        case False{}:
          suffix_step(h, t, Fetch.is_prefix(Fetch.sep(), t), suffix_go(t, Fetch.is_prefix(Fetch.sep(), t)))

def Laws.body_suffix(s):
  suffix_go(s, Fetch.is_prefix(Fetch.sep(), s))

# No blank line
# -------------

# the no-body law over both walkers, at every state
def none_go(s: String, e: Bool, hy: {True{} == Fetch.no_sep.go(s, e) : Bool}) -> {Fetch.http_body.go(s, e) == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, +t}:
      match e:
        case True{}:
          %hy : BD(_, Unit, {Fetch.drop(3n, t) == "" : String})
          Unit{}
        case False{}:
          none_go(t, Fetch.is_prefix(Fetch.sep(), t), hy)

def Laws.body_none(s, e):
  none_go(s, Fetch.is_prefix(Fetch.sep(), s), e)

# After the headers
# -----------------

# the flag at a character only looks 4 characters ahead: it is the same
# in front of "\r\n\r" and in front of "\r\n\r" ++ x
def agree(+c: Char, t: String, -x: String)
  -> {Fetch.is_prefix(Fetch.sep(), SCon{c, t ++ "\r\n\r"}) == Fetch.is_prefix(Fetch.sep(), SCon{c, t ++ ("\r\n\r" ++ x)}) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{d, t2}:
      match t2:
        case SNil{}:
          {==}
        case SCon{f, t3}:
          match t3:
            case SNil{}:
              {==}
            case SCon{g, r}:
              {==}

# the step: with the flag x decided, a set flag contradicts no_sep of
# the headers, and a clear flag advances both walkers
def step(+c: Char, +t: String, +b: String, x: Bool,
  hy: {True{} == Fetch.no_sep.go(SCon{c, t ++ "\r\n\r"}, x) : Bool},
  ih: {True{} == Fetch.no_sep(t ++ "\r\n\r") : Bool} -> {Fetch.http_body(t ++ ("\r\n\r\n" ++ b)) == b : String})
  -> {Fetch.http_body.go(SCon{c, t ++ ("\r\n\r\n" ++ b)}, x) == b : String}:
  match x:
    case True{}:
      %hy : BD(_, Unit, {Fetch.drop(3n, t ++ ("\r\n\r\n" ++ b)) == b : String})
      Unit{}
    case False{}:
      ih(hy)

def Laws.body_after_headers(h, b, e):
  match h:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %agree(c, t, "\n" ++ b) : {Fetch.http_body.go(SCon{c, t ++ ("\r\n\r\n" ++ b)}, _) == b : String}
      step(c, t, b, Fetch.is_prefix(Fetch.sep(), SCon{c, t ++ "\r\n\r"}), e, e2 => Laws.body_after_headers(t, b, e2))

def Laws.body_example():
  {==}
