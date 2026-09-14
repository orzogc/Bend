# Hello world: the smallest IO program. greeting() is its pure part
# and main prints it. Try it:
#
#   bend demos/io_hello_world/main.bend
import Base

def greeting() -> String:
  "Hello, world!"

def main() -> IO(Unit):
  IO.print(greeting())
