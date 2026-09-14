# The laws of the echo server. They pin echo_data, the pure part of
# the program: the reading of a recv result that decides whether the
# handler echoes or closes. PROOF.bend must prove them.
import Base
import ./main.bend as Echo

# LAW: a failed recv reads as a closed peer: there is nothing to echo.
law data_of_fail:
  for e: U32 & String
  {Echo.echo_data(Fail{e}) == "" : String}

# LAW: the data of a good recv is echoed as it came, byte for byte.
law data_of_done:
  for s: String
  {Echo.echo_data(Done{s}) == s : String}
