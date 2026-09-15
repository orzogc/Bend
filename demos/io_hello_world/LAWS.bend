# The laws of the hello world. They pin greet, the pure part of the
# program, for EVERY name: the greeting is 8 characters longer than
# the name, it ends with '!', and it determines the name (two equal
# greetings come from equal names). PROOF.bend must prove them.
import Base
import ./main.bend as Hello

# LAW: the greeting of a name has 8 more characters than the name:
# 7 for "Hello, " and 1 for "!".
law greet_length:
  for name: String
  {8n+Hello.length(name) == Hello.length(Hello.greet(name)) : Nat}

# LAW: the greeting of any name ends with '!', whatever default the
# last-character measure gets for the empty string.
law greet_last:
  for  name: String
  for -d: Char
  {Hello.last(Hello.greet(name), d) == '!' : Char}

# LAW: the greeting determines the name: when two names give the same
# greeting, they are the same name.
law greet_inj:
  for  a: String
  for  b: String
  for +e: {Hello.greet(a) == Hello.greet(b) : String}
  {a == b : String}

# LAW: the greeting of "world" is "Hello, world!" (closed, by
# evaluation).
law greet_world:
  {Hello.greet("world") == "Hello, world!" : String}
