# The VibiNet relay: one process, every room. PORT picks the port
# (default 7777). See the Server section of vibinet.bend.
#
#   bend demos/vibinet/server.bend -o relay && ./relay
import Base
import ./vibinet.bend as Net

def main() -> IO(Unit):
  do IO<Unit>:
    port : String <- Net.Env.get("PORT", "7777")
    Net.Server.run(Net.Env.u32(port, 7777))
