# The proofs of the echo server laws. This file imports the server
# (as Echo) and the claims (as Laws) and fills every law. echoes_all
# is an induction over the frames: a frame without data refutes the
# hypothesis (True is not False), a frame with data is sent and the
# rest is the induction hypothesis. close_ends is an induction over
# the frames before the close: each one makes the same move on both
# sides. sent_is_received builds its witness by induction: the unsent
# tail is the whole rest at a close, else the tail the rest gives,
# with the append law re-bracketing the bytes. The sanity laws
# compute.
import Base
import ./main.bend as Echo
import ./LAWS.bend as Laws

# BD(b, t, f) picks a type by a Bool, so a rewrite through it refutes
# a clash between True{} and False{}
def BD(b: Bool, tc: Type, fc: Type) -> Type:
  match b:
    case True{}:
      tc
    case False{}:
      fc

# Every frame with data is sent back
# ----------------------------------

def Laws.echoes_all(frames, h):
  match frames:
    case Nil{}:
      {==}
    case SNil{} <> rest:
      %h : BD(_, Unit, {Echo.echo(SNil{} <> rest) == SNil{} <> rest : List<&2, String>})
      Unit{}
    case SCon{c, t} <> rest:
      %Laws.echoes_all(rest, h)
        : {SCon{c, t} <> Echo.echo(rest) == SCon{c, t} <> _ : List<&2, String>}
      {==}

# A close ends the conversation
# -----------------------------

def Laws.close_ends(pre, post):
  match pre:
    case Nil{}:
      {==}
    case d <> rest:
      %Laws.close_ends(rest, post)
        : {Echo.echo(d <> Echo.cat(rest, "" <> post)) == Echo.echo_go(Echo.echo_step(d), _)
           : List<&2, String>}
      {==}

# The bytes sent are a prefix of the bytes read
# ---------------------------------------------

law append_assoc:
  for a: String
  for -b: String
  for -c: String
  {a ++ (b ++ c) == (a ++ b) ++ c : String}

def append_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %append_assoc(t, b, c) : {SCon{h, t ++ (b ++ c)} == SCon{h, _} : String}
      {==}

# the step: the tail of the rest becomes the tail of the whole
law sent_step:
  for d: String
  for +rest: List<&2, String>
  for w: &r: String -> {Echo.concat(rest) == Echo.concat(Echo.echo(rest)) ++ r : String}
  exs r: String
  {Echo.concat(d <> rest) == Echo.concat(Echo.echo(d <> rest)) ++ r : String}

def sent_step(d, rest, w):
  match d:
    case SNil{}:
      (Echo.concat(rest), {==})
    case SCon{h, t}:
      (r, e) = w
      (r,
        %append_assoc(t, Echo.concat(Echo.echo(rest)), r)
          : {SCon{h, t ++ Echo.concat(rest)} == SCon{h, _} : String}
        %e : {SCon{h, t ++ Echo.concat(rest)} == SCon{h, t ++ _} : String}
        {==})

def Laws.sent_is_received(frames):
  match frames:
    case Nil{}:
      ("", {==})
    case d <> rest:
      sent_step(d, rest, Laws.sent_is_received(rest))

# Sanity
# ------

def Laws.data_of_fail(e):
  {==}

def Laws.data_of_done(s):
  {==}
