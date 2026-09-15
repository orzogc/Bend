# The laws of the echo server. They pin echo, the connection as a
# pure function of the frames it reads (main.bend, Spec): the step the
# handler runs on every recv, folded over a list of frames. Three
# general claims, over any list of frames, say what the server sends:
# everything it got while the peer kept sending, nothing past a close,
# and never a byte it did not receive. PROOF.bend must prove them.
import Base
import ./main.bend as Echo

# LAW: while the peer keeps sending data, the server sends back
# exactly what it received, frame by frame, in order: for any list of
# frames that all carry data, the frames sent are the frames read.
law echoes_all:
  for frames: List<&2, String>
  for h: {True{} == Echo.all_data(frames) : Bool}
  {Echo.echo(frames) == frames : List<&2, String>}

# LAW: a closed peer or a failed recv (both read as "") ends the
# conversation: nothing past that frame is sent, whatever the frames
# before it and after it.
law close_ends:
  for pre: List<&2, String>
  for post: List<&2, String>
  {Echo.echo(Echo.cat(pre, "" <> post)) == Echo.echo(pre) : List<&2, String>}

# LAW: the server never sends a byte it did not receive: for any
# frames, the bytes it sends are a prefix of the bytes it read, in
# order (the rest is the unsent tail).
law sent_is_received:
  for +frames: List<&2, String>
  exs rest: String
  {Echo.concat(frames) == Echo.concat(Echo.echo(frames)) ++ rest : String}

# LAW: a failed recv reads as a closed peer: there is nothing to echo
# (sanity).
law data_of_fail:
  for e: U32 & String
  {Echo.echo_data(Fail{e}) == "" : String}

# LAW: the data of a good recv is echoed as it came, byte for byte
# (sanity).
law data_of_done:
  for s: String
  {Echo.echo_data(Done{s}) == s : String}
