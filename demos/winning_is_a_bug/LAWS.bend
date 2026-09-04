# The laws. The human states them; CERT.bend must prove them.

import Base
import ./main.bend as Game

# LAW: for any sequence of moves, replaying them
# from the start can never lead to victory.
law winning_is_a_bug:
  for moves: List<Game.Move>
  board = Game.replay(Game.start(), moves)
  {Game.is_won(board) == False{} : Bool}
