# The proofs of the hello world laws. greet(name) unfolds to the seven
# characters of "Hello, " in front of name ++ "!", so every proof is
# about the part after the seventh character: name ++ "!".
#
# greet_length is an induction on the name: each character adds one on
# both sides, and the induction hypothesis closes the rest.
# greet_last generalizes the default (last_snoc): walking name ++ "!"
# carries the last character seen, and the end is '!'.
# greet_inj is an induction on both names: an empty name against a
# non-empty one is refuted, since "!" is never a longer string, and
# two non-empty names are equal when their heads and tails are, the
# tails by the induction hypothesis.
import Base
import ./main.bend as Hello
import ./LAWS.bend as Laws

# Length
# ------

def Laws.greet_length(name):
  match name:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Laws.greet_length(t) : {9n+Hello.length(t) == 1n+_ : Nat}
      {==}

# Last character
# --------------

# the last character of name ++ "!" is '!', whatever default is given
def last_snoc(name: String, -d: Char) -> {Hello.last(name ++ "!", d) == '!' : Char}:
  match name:
    case SNil{}:
      {==}
    case SCon{c, t}:
      last_snoc(t, c)

def Laws.greet_last(name, d):
  last_snoc(name, ' ')

# Injectivity
# -----------

# disc(s) picks a type by the shape of a string, so a rewrite through
# it refutes SNil{} == SCon{..}
def disc(s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{h, t}:
      Empty

# no string followed by "!" is empty
def snoc_not_nil(t: String, e: {SNil{} == t ++ "!" : String}) -> Empty:
  match t:
    case SNil{}:
      %e : disc(_)
      Unit{}
    case SCon{h, r}:
      %e : disc(_)
      Unit{}

# the part of a greeting after "Hello, ": name ++ "!"
def after(s: String) -> String:
  Hello.drop(7n, s)

def Laws.greet_inj(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{+c, +t}:
      Empty.absurd({SNil{} == SCon{c, t} : String},
        snoc_not_nil(t, Equal.cong(String, String, s => Hello.drop(8n, s), Hello.greet(SNil{}), Hello.greet(SCon{c, t}), e)))
    case SCon{+c, +t} SNil{}:
      Empty.absurd({SCon{c, t} == SNil{} : String},
        snoc_not_nil(t, Equal.cong(String, String, s => Hello.drop(8n, s), Hello.greet(SNil{}), Hello.greet(SCon{c, t}),
          Equal.sym(String, Hello.greet(SCon{c, t}), Hello.greet(SNil{}), e))))
    case SCon{+c1, +t1} SCon{+c2, +t2}:
      %Laws.greet_inj(t1, t2, Equal.cong(String, String, s => "Hello, " ++ Hello.drop(8n, s), Hello.greet(SCon{c1, t1}), Hello.greet(SCon{c2, t2}), e)) : {SCon{c1, t1} == SCon{c2, _} : String}
      %e : {SCon{c1, t1} == SCon{Hello.head(after(_), c1), t1} : String}
      {==}

def Laws.greet_world():
  {==}
