# Fly -- the laws. Claims about the flight's pure control logic: Esc
# and the close button quit, the held word tracks the keys, the fps
# counter counts frames per second, and the fps digits blank their
# leading zeros. The F32 scene is not claimed. PROOF.bend must prove
# every one.
import Base
import ./main.bend as Ray

# LAW: Esc pressed quits: Fly.key on code 27 down gives None for any
# state, and so does the close button.
law quits:
  for +s: Ray.Fly
  {Ray.Fly.key(27, True{}, s) == None{} : Maybe<Ray.Fly>}
  & {Ray.Fly.event(Close{}, s) == None{} : Maybe<Ray.Fly>}

# LAW: the held word tracks the keys: pressing W on an empty word sets
# bit 1; pressing W and releasing it restores a word that holds Left
# (64); Esc (27) has no bit, so it never moves the camera.
law held_word:
  {Ray.Fly.press(True{}, 0, Ray.Fly.mask(119)) == 1 : U32}
  & {Ray.Fly.press(False{}, Ray.Fly.press(True{}, 64, Ray.Fly.mask(119)),
      Ray.Fly.mask(119)) == 64 : U32}
  & {Ray.Fly.mask(27) == 0 : U32}

# LAW: the fps counter: a tick within the second (999 ms after t0) adds
# a frame and keeps the count; a tick at the next second (1000 ms)
# makes the frames the count, restarts them at 0 and moves t0. For any
# position, angles and held word.
law fps_counter:
  for x: F32
  for y: F32
  for z: F32
  for yaw: F32
  for pitch: F32
  for held: U32
  for frames: U32
  for fps: U32
  {Ray.Fly.clock(999n, Ray.Fly{x, y, z, yaw, pitch, held, 0n, frames, fps})
    == Ray.Fly{x, y, z, yaw, pitch, held, 0n, (frames + 1 : U32), fps}
    : Ray.Fly}
  & {Ray.Fly.clock(1000n, Ray.Fly{x, y, z, yaw, pitch, held, 0n, 7, fps})
    == Ray.Fly{x, y, z, yaw, pitch, held, 1000n, 0, 8} : Ray.Fly}

# LAW: the fps digits: a count under 10 blanks its two leading digits
# (glyph 10, the empty one, for any digit it would show) and shows its
# units; 123 shows 1, 2, 3.
law fps_digits:
  for d: U32
  {Ray.Fly.glyph(U32.to_nat(Ray.Fly.lead(True{}, d))) == 0 : U32}
  & {Ray.Fly.digit(0n, 7) == 10 : U32}
  & {Ray.Fly.digit(1n, 7) == 10 : U32}
  & {Ray.Fly.digit(2n, 7) == 7 : U32}
  & {Ray.Fly.digit(0n, 123) == 1 : U32}
  & {Ray.Fly.digit(1n, 123) == 2 : U32}
  & {Ray.Fly.digit(2n, 123) == 3 : U32}
