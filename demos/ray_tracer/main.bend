# Fly: a ray-marched field of spheres on a checkered plane under a sky,
# one light and hard shadows, flown with W/A/S/D (forward, left, back,
# right, relative to the yaw), Q/E (up, down), the arrows left/right
# (turn) and up/down (look up, down); Esc or the close button quits.
# The held keys are bits of one word (1 W, 2 A, 4 S, 8 D, 16 Q, 32 E,
# 64 Left, 128 Right, 256 Up, 512 Down). The top-left corner counts the
# frames per second (IO.now once per tick; the count of the last whole
# second, in a 3 x 5 font). Every pixel differs, so a frame is the
# full-detail quadtree to depth 10 (1024 x 1024, the window shows its
# top 1024 x 768): Fly.scene! builds it on the GPU, the ONE bang in the
# file, and a machine without a GPU runs the same bang on the host
# pool. F32 math only; the camera basis is a flat Data record built
# once per frame (Fly.Cam), so the fork shares twelve words and no
# refcount. Each march loop takes its stop as a parameter the previous
# step computed, so the recursion is one def descending on the budget.
#
#   bend demos/ray_tracer/main.bend -o ray_tracer && ./ray_tracer
import Base

type Fly is Data:
  Fly{x: F32, y: F32, z: F32, yaw: F32, pitch: F32, held: U32, t0: Nat,
    frames: U32, fps: U32}

type Fly.Cam is Data:
  Cam{ex: F32, ey: F32, ez: F32, fx: F32, fy: F32, fz: F32, rx: F32, rz: F32,
    ux: F32, uy: F32, uz: F32, fps: U32}

def Fly.init() -> Fly:
  Fly{0.0, 1.5, (0.0 - 6.0 : F32), 0.0, 0.0, 0, 0n, 0, 0}

def Fly.pick(c: Bool, a: F32, b: F32) -> F32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Fly.min(+a: F32, +b: F32) -> F32:
  Fly.pick((a < b : F32), a, b)

def Fly.max(+a: F32, +b: F32) -> F32:
  Fly.pick((a < b : F32), b, a)

def Fly.clamp01(+x: F32) -> F32:
  Fly.min(1.0, Fly.max(0.0, x))

def Fly.bit(b: Bool, v: U32) -> U32:
  match b:
    case True{}:
      v
    case False{}:
      0

def Fly.onef(b: Bool) -> F32:
  match b:
    case True{}:
      1.0
    case False{}:
      0.0

def Fly.bitf(+held: U32, m: U32) -> F32:
  Fly.onef(U32.is_ne((held .&. m : U32), 0))

def Fly.mask(+code: U32) -> U32:
  (Fly.bit(U32.is_eq(code, 119), 1) .|. Fly.bit(U32.is_eq(code, 97), 2)
    .|. Fly.bit(U32.is_eq(code, 115), 4) .|. Fly.bit(U32.is_eq(code, 100), 8)
    .|. Fly.bit(U32.is_eq(code, 113), 16) .|. Fly.bit(U32.is_eq(code, 101), 32)
    .|. Fly.bit(U32.is_eq(code, 63234), 64)
    .|. Fly.bit(U32.is_eq(code, 63235), 128)
    .|. Fly.bit(U32.is_eq(code, 63232), 256)
    .|. Fly.bit(U32.is_eq(code, 63233), 512) : U32)

def Fly.press(down: Bool, held: U32, mask: U32) -> U32:
  match down:
    case True{}:
      (held .|. mask : U32)
    case False{}:
      (held .&. U32.not(mask) : U32)

def Fly.quit(esc: Bool, s: Fly) -> Maybe<Fly>:
  match esc:
    case True{}:
      None{}
    case False{}:
      Some{s}

def Fly.key(+code: U32, +down: Bool, s: Fly) -> Maybe<Fly>:
  Fly{x, y, z, yaw, pitch, held, t0, frames, fps} = s
  Fly.quit(Bool.and(down, U32.is_eq(code, 27)),
    Fly{x, y, z, yaw, pitch, Fly.press(down, held, Fly.mask(code)), t0, frames,
      fps})

def Fly.event(e: Event, s: Fly) -> Maybe<Fly>:
  match e:
    case Key{code, down}:
      Fly.key(code, down, s)
    case Mouse{x, y, button, down}:
      Some{s}
    case Move{x, y}:
      Some{s}
    case Close{}:
      None{}

def Fly.events(events: List<Event>, s: Fly) -> Maybe<Fly>:
  match events:
    case Nil{}:
      Some{s}
    case e <> rest:
      Maybe.bind(&1, Fly, Fly, Fly.event(e, s), s2 => Fly.events(rest, s2))

def Fly.step(+s: Fly) -> Fly:
  Fly{x, y, z, yaw, pitch, held, t0, frames, fps} = s
  +fwd = (Fly.bitf(held, 1) - Fly.bitf(held, 4) : F32)
  +side = (Fly.bitf(held, 8) - Fly.bitf(held, 2) : F32)
  +rise = (Fly.bitf(held, 16) - Fly.bitf(held, 32) : F32)
  +turn = (Fly.bitf(held, 128) - Fly.bitf(held, 64) : F32)
  +tilt = (Fly.bitf(held, 256) - Fly.bitf(held, 512) : F32)
  +yaw2 = (yaw + 0.03 * turn : F32)
  Fly{(x + 0.08 * (fwd * F32.sin(yaw2) + side * F32.cos(yaw2)) : F32),
    Fly.max(0.3, (y + 0.08 * rise : F32)),
    (z + 0.08 * (fwd * F32.cos(yaw2) - side * F32.sin(yaw2)) : F32), yaw2,
    Fly.min(1.4, Fly.max((0.0 - 1.4 : F32), (pitch + 0.02 * tilt : F32))), held,
    t0, frames, fps}

def Fly.count(within: Bool, now: Nat, s: Fly) -> Fly:
  match within:
    case True{}:
      s
    case False{}:
      Fly{x, y, z, yaw, pitch, held, t0, frames, fps} = s
      Fly{x, y, z, yaw, pitch, held, now, 0, frames}

def Fly.clock(+now: Nat, +s: Fly) -> Fly:
  Fly{x, y, z, yaw, pitch, held, t0, frames, fps} = s
  Fly.count(Nat.is_lt(Nat.sub(now, t0), 1000n), now,
    Fly{x, y, z, yaw, pitch, held, t0, (frames + 1 : U32), fps})

def Fly.after(now: Nat, m: Maybe<Fly>) -> Maybe<Fly>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{Fly.clock(now, Fly.step(s))}

def Fly.tick(events: List<Event>, s: Fly) -> IO(Maybe<Fly>):
  do IO<Maybe<Fly>>:
    now : Nat <- IO.now()
    IO.pure(Maybe<Fly>, Fly.after(now, Fly.events(events, s)))

def Fly.sdf(+px: F32, +py: F32, +pz: F32) -> F32:
  +qx = (px - 4.0 * F32.floor((px / 4.0 : F32)) - 2.0 : F32)
  +qz = (pz - 4.0 * F32.floor((pz / 4.0 : F32)) - 2.0 : F32)
  +qy = (py - 1.0 : F32)
  Fly.min(py, (F32.sqrt((qx * qx + qy * qy + qz * qz : F32)) - 1.0 : F32))

def Fly.march(
  i: Nat, stop: Bool, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32,
  +dz: F32, +t: F32
) -> F32:
  match i:
    case 0n:
      t
    case 1n+k:
      match stop:
        case True{}:
          t
        case False{}:
          +d = Fly.sdf((ox + t * dx : F32), (oy + t * dy : F32),
            (oz + t * dz : F32))
          +t2 = (t + d : F32)
          Fly.march(k, ((d < 0.002) || (t2 > 60.0) : F32), ox, oy, oz, dx, dy,
            dz, t2)

def Fly.pack(+r: F32, +g: F32, +b: F32) -> U32:
  (F32.to_u32((255.0 * Fly.clamp01(r) : F32)) << 16n
    .|. F32.to_u32((255.0 * Fly.clamp01(g) : F32)) << 8n
    .|. F32.to_u32((255.0 * Fly.clamp01(b) : F32)) : U32)

def Fly.sky(+dy: F32) -> U32:
  +u = Fly.clamp01((dy * 2.0 : F32))
  Fly.pack((0.75 - 0.45 * u : F32), (0.85 - 0.35 * u : F32), 1.0)

def Fly.checker(+px: F32, +pz: F32) -> F32:
  +c = (F32.floor(px) + F32.floor(pz) : F32)
  Fly.pick(F32.is_eq((c - 2.0 * F32.floor((c * 0.5 : F32)) : F32), 0.0), 0.9,
    0.35)

def Fly.lit(shadow: Bool, +diffuse: F32) -> F32:
  match shadow:
    case True{}:
      0.15
    case False{}:
      (0.15 + 0.85 * diffuse : F32)

def Fly.surface(
  +px: F32, +py: F32, +pz: F32, +nx: F32, +ny: F32, +nz: F32, +t: F32
) -> U32:
  +diffuse = Fly.max(0.0, (nx * 0.4082 + ny * 0.8165 - nz * 0.4082 : F32))
  +shade = Fly.march(48n, False{}, (px + nx * 0.02 : F32),
    (py + ny * 0.02 : F32), (pz + nz * 0.02 : F32), 0.4082, 0.8165,
    (0.0 - 0.4082 : F32), 0.05)
  +light = Fly.lit((shade < 60.0 : F32), diffuse)
  +fog = Fly.clamp01((t * 0.03 : F32))
  +ground = (py < 0.02 : F32)
  +r = Fly.pick(ground, Fly.checker(px, pz), 0.9)
  +g = Fly.pick(ground, Fly.checker(px, pz), 0.4)
  +b = Fly.pick(ground, Fly.checker(px, pz), 0.3)
  Fly.pack((r * light + (0.75 - r * light) * fog : F32),
    (g * light + (0.85 - g * light) * fog : F32),
    (b * light + (1.0 - b * light) * fog : F32))

def Fly.hit(
  miss: Bool, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32,
  +t: F32
) -> U32:
  match miss:
    case True{}:
      Fly.sky(dy)
    case False{}:
      +px = (ox + t * dx : F32)
      +py = (oy + t * dy : F32)
      +pz = (oz + t * dz : F32)
      +nx = (Fly.sdf((px + 0.001 : F32), py, pz)
        - Fly.sdf((px - 0.001 : F32), py, pz) : F32)
      +ny = (Fly.sdf(px, (py + 0.001 : F32), pz)
        - Fly.sdf(px, (py - 0.001 : F32), pz) : F32)
      +nz = (Fly.sdf(px, py, (pz + 0.001 : F32))
        - Fly.sdf(px, py, (pz - 0.001 : F32)) : F32)
      +il = (1.0 / F32.sqrt((nx * nx + ny * ny + nz * nz : F32)) : F32)
      Fly.surface(px, py, pz, (nx * il : F32), (ny * il : F32), (nz * il : F32),
        t)

def Fly.ray(+ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32) -> U32:
  +t = Fly.march(96n, False{}, ox, oy, oz, dx, dy, dz, 0.0)
  Fly.hit((t > 60.0 : F32), ox, oy, oz, dx, dy, dz, t)

def Fly.cast(+x: U32, +y: U32, +cam: Fly.Cam) -> U32:
  Cam{ex, ey, ez, fx, fy, fz, rx, rz, ux, uy, uz, fps} = cam
  +sx = ((U32.to_f32(x) - 511.5) / 640.0 : F32)
  +sy = ((383.5 - U32.to_f32(y)) / 640.0 : F32)
  +vx = (fx + sx * rx + sy * ux : F32)
  +vy = (fy + sy * uy : F32)
  +vz = (fz + sx * rz + sy * uz : F32)
  +il = (1.0 / F32.sqrt((vx * vx + vy * vy + vz * vz : F32)) : F32)
  Fly.ray(ex, ey, ez, (vx * il : F32), (vy * il : F32), (vz * il : F32))

def Fly.glyph(d: Nat) -> U32:
  match d:
    case 0n:
      480599
    case 1n:
      467506
    case 2n:
      464711
    case 3n:
      476999
    case 4n:
      280405
    case 5n:
      476951
    case 6n:
      481047
    case 7n:
      279623
    case 8n:
      481111
    case 9n:
      477015
    case _:
      0

def Fly.lead(blank: Bool, d: U32) -> U32:
  match blank:
    case True{}:
      10
    case False{}:
      d

def Fly.digit(i: Nat, +fps: U32) -> U32:
  match i:
    case 0n:
      Fly.lead((fps < 100 : U32), (fps / 100 : U32))
    case 1n:
      Fly.lead((fps < 10 : U32), (fps / 10 % 10 : U32))
    case _:
      (fps % 10 : U32)

def Fly.hud(+x: U32, +y: U32, +fps: U32) -> U32:
  +bit = U32.to_nat((y / 8 * 4 + x % 32 / 8 : U32))
  (16777215 * (Fly.glyph(U32.to_nat(Fly.digit(U32.to_nat((x / 32 : U32)), fps)))
    >> bit .&. 1) : U32)

def Fly.over(hud: Bool, +x: U32, +y: U32, +cam: Fly.Cam) -> U32:
  match hud:
    case True{}:
      Cam{ex, ey, ez, fx, fy, fz, rx, rz, ux, uy, uz, fps} = cam
      Fly.hud(x, y, fps)
    case False{}:
      Fly.cast(x, y, cam)

def Fly.shade(+x: U32, +y: U32, +cam: Fly.Cam) -> U32:
  Fly.over(((x < 96) && (y < 40) : U32), x, y, cam)

def Fly.scene(+d: Nat, +x: U32, +y: U32, +cam: Fly.Cam) -> Image:
  match d:
    case 0n:
      Pix{Fly.shade(x, y, cam)}
    case 1n+e:
      +h = U32.shln(1, e)
      +x1 = U32.add(x, h)
      +y1 = U32.add(y, h)
      tl tr bl br = Fly.scene(e, x, y, cam) Fly.scene(e, x1, y, cam)
        Fly.scene(e, x, y1, cam) Fly.scene(e, x1, y1, cam)
      Qua{tl, tr, bl, br}

def Fly.camera(+s: Fly) -> Fly.Cam:
  Fly{x, y, z, yaw, pitch, held, t0, frames, fps} = s
  +sy = F32.sin(yaw)
  +cy = F32.cos(yaw)
  +sp = F32.sin(pitch)
  +cp = F32.cos(pitch)
  Cam{x, y, z, (sy * cp : F32), sp, (cy * cp : F32), cy, (0.0 - sy : F32),
    (0.0 - sp * sy : F32), cp, (0.0 - sp * cy : F32), fps}

def Fly.view(s: Fly) -> Fly & Image:
  +s2 = s
  (s2, Fly.scene!(10n, 0, 0, Fly.camera(s2)))

def main() -> IO(Unit):
  App.run(~Fly, ~App{Fly.view, Fly.tick}, "Fly", 1024, 768, Fly.init())
