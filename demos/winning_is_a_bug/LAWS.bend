# The laws. The human states them; CERT.bend must prove them.

import Base
import ./main.bend as Game

# LAW: for any sequence of moves, applying it
# to the initial board can never lead to victory.
assert winning_is_a_bug:
  forall moves: List<Game.Move>
  board = Game.apply(Game.init(), moves)
  {Game.is_won(board) == False{} : Bool}
