# The proofs of the HTTP client laws. The two closed laws close by
# evaluation. body_rest opens the text: the walker answers it at once
# when its flag is set. body_suffix is suffix_go at the start state:
# an induction over the text that carries the window state along and
# builds the prefix one character at a time.
import Base
import ./main.bend as Fetch
import ./LAWS.bend as Laws

def Laws.body_after_headers():
  {==}

def Laws.body_none():
  {==}

def Laws.body_rest(s, w):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{a}, t}:
      {==}

# the step of the suffix law: the prefix grows by the character the
# walker consumed, and the induction hypothesis closes the rest
law suffix_step:
  for  a: U32
  for -w: U32
  for -t: String
  for ih: (&p: String -> {p ++ Fetch.http_body.go(t, U32.is_eq((w * 256 + a : U32), 218762506), (w * 256 + a : U32)) == t : String})
  exs p: String
  {p ++ Fetch.http_body.go(SCon{Chr{a}, t}, False{}, w) == SCon{Chr{a}, t} : String}

def suffix_step(a, w, t, ih):
  (p, pf) = ih
  (SCon{Chr{a}, p}, Equal.cong(String, String, x => SCon{Chr{a}, x}, p ++ Fetch.http_body.go(t, U32.is_eq((w * 256 + a : U32), 218762506), (w * 256 + a : U32)), t, pf))

# the suffix law over the walker, at every window state
law suffix_go:
  for s: String
  for e: Bool
  for w: U32
  exs p: String
  {p ++ Fetch.http_body.go(s, e, w) == s : String}

def suffix_go(s, e, w):
  match s:
    case SNil{}:
      ("", {==})
    case SCon{Chr{+a}, t}:
      match e:
        case True{}:
          ("", {==})
        case False{}:
          +w2 = (w * 256 + a : U32)
          suffix_step(a, w, t, suffix_go(t, U32.is_eq(w2, 218762506), w2))

def Laws.body_suffix(s):
  suffix_go(s, False{}, 0)
