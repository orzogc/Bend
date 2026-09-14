# The proofs of the echo server laws. echo_data matches its result
# once, so each law holds by evaluation on the constructor it names.
import Base
import ./main.bend as Echo
import ./LAWS.bend as Laws

def Laws.data_of_fail(e):
  {==}

def Laws.data_of_done(s):
  {==}
