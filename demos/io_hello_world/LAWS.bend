# The laws of the hello world. They pin greeting(), the pure part of
# the program: its text, its first character and its last one.
# PROOF.bend must prove them.
import Base
import ./main.bend as Hello

# LAW: the greeting is "Hello, world!".
law greeting_text:
  {Hello.greeting() == "Hello, world!" : String}

# LAW: the greeting starts with 'H': some rest follows that character.
law greeting_head:
  exs rest: String
  {Hello.greeting() == SCon{'H', rest} : String}

# LAW: the greeting ends with '!': some start precedes that character.
law greeting_last:
  exs start: String
  {Hello.greeting() == start ++ "!" : String}
