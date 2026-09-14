# Slash Bros 3D: the render core under the original's stage, hero and
# light. The host builds the scene: every surface (a unit shape in a
# basis, a cloth sheet, a ring, the cliff, an arch) is a grid of
# patches, fewer when small on the screen; a triangle on the screen
# carries its barycentric, depth and colour planes (Gouraud: a vertex
# is lit by the original's lights, GGX with Schlick and Smith, ACES,
# gamma; a transparent one is unlit) and goes in every 64-cell it
# meets, a quadtree over the 2048 root (the window shows its top-left
# 1920 x 1200). ONE bang, Frame.node!, borrows the tree on the device
# as a fork tree down to the cells and their 16 tiles (a tile nothing
# crosses is one Pix); the last frame's image goes down the same tree
# and each tile drops its own; the host frees the scene beside the
# next build. A tile filters the cell's list into its opaque and
# transparent lists and walks them once per 4 x 4 square: the nearest
# opaque wins at each pixel, the sky where none, then the transparent
# ones nearer than it blend over; a 2 x 2 block under one opaque
# triangle, or of one colour, is one Pix. The camera is the original's
# lens (a spring after the hero and the boss) and eye (x, y + 3.2, 27)
# looking at (x, y, 0), focal 51840 / width about (960, 581). The sim
# is the original's hero side at 60 Hz (WASD or arrows move, I jumps,
# J and K attack, L guards or dodges, P pauses, R restarts, Esc quits)
# against THE SEVERANT (Boss), with the effects (Effects) and the sound
# (Sound); the view lies between the last two ticks. The title shows
# the frame rate twice a second. SLASH_PROBE=N runs N frames of a
# scripted fight headless and prints the state every 60 ticks, every
# cue with its tick and the microseconds a frame of each stage;
# SLASH_DUMP=T then prints the frame at tick T as a tree (Q, or a
# colour); SLASH_MODE=M rigs the mode (9: the parry cue); SLASH_WAV=
# path writes the mix there as text (a line a block, each sample's
# bits) instead of feeding the device; SLASH_VOICES=N adds N looping
# voices to load the mixer.
#
#   bend demos/slash_bros_3d/main.bend -o slash && ./slash
import Base

# Math
# ----

type Vec is Data:
  Vec{x: F32, y: F32, z: F32}

def Math.pick(c: Bool, a: F32, b: F32) -> F32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Math.word(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Bool.pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def Math.min(+a: F32, +b: F32) -> F32:
  Math.pick((a < b : F32), a, b)

def Math.max(+a: F32, +b: F32) -> F32:
  Math.pick((a < b : F32), b, a)

def Math.clamp(+x: F32, +lo: F32, +hi: F32) -> F32:
  Math.min(hi, Math.max(lo, x))

def Math.sat(+x: F32) -> F32:
  Math.clamp(x, 0.0, 1.0)

def Math.mix(+a: F32, +b: F32, +t: F32) -> F32:
  (a + (b - a) * t : F32)

def Math.smooth(+x: F32) -> F32:
  +u = Math.sat(x)
  (u * u * (3.0 - 2.0 * u) : F32)

def Math.pack(+r: F32, +g: F32, +b: F32) -> U32:
  (F32.to_u32((255.0 * Math.sat(r) : F32)) << 16n
    .|. F32.to_u32((255.0 * Math.sat(g) : F32)) << 8n
    .|. F32.to_u32((255.0 * Math.sat(b) : F32)) : U32)

def Math.chan(+c: U32, n: Nat) -> F32:
  (U32.to_f32((c >> n .&. 255 : U32)) / 255.0 : F32)

def Vec.add(+a: Vec, +b: Vec) -> Vec:
  Vec{ax, ay, az} = a
  Vec{bx, by, bz} = b
  Vec{(ax + bx : F32), (ay + by : F32), (az + bz : F32)}

def Vec.sub(+a: Vec, +b: Vec) -> Vec:
  Vec{ax, ay, az} = a
  Vec{bx, by, bz} = b
  Vec{(ax - bx : F32), (ay - by : F32), (az - bz : F32)}

def Vec.scale(+a: Vec, +k: F32) -> Vec:
  Vec{x, y, z} = a
  Vec{(x * k : F32), (y * k : F32), (z * k : F32)}

def Vec.dot(+a: Vec, +b: Vec) -> F32:
  Vec{ax, ay, az} = a
  Vec{bx, by, bz} = b
  (ax * bx + ay * by + az * bz : F32)

def Vec.cross(+a: Vec, +b: Vec) -> Vec:
  Vec{ax, ay, az} = a
  Vec{bx, by, bz} = b
  Vec{(ay * bz - az * by : F32), (az * bx - ax * bz : F32),
    (ax * by - ay * bx : F32)}

def Vec.len(+v: Vec) -> F32:
  F32.sqrt(Vec.dot(v, v))

def Vec.unit(+v: Vec) -> Vec:
  Vec.scale(v, (1.0 / Math.max(0.00001, Vec.len(v)) : F32))

def Vec.mix(+a: Vec, +b: Vec, +t: F32) -> Vec:
  Vec{ax, ay, az} = a
  Vec{bx, by, bz} = b
  Vec{Math.mix(ax, bx, t), Math.mix(ay, by, t), Math.mix(az, bz, t)}

# Turned about y by an angle (0 faces +x, pi faces -x).
def Vec.turn(+v: Vec, +face: F32) -> Vec:
  Vec{x, y, z} = v
  +c = F32.cos(face)
  +s = F32.sin(face)
  Vec{(x * c + z * s : F32), y, (z * c - x * s : F32)}

def Vec.rgb(+c: U32) -> Vec:
  Vec{Math.chan(c, 16n), Math.chan(c, 8n), Math.chan(c, 0n)}

# Camera
# ------

# The eye, the focal length in pixels, the contact point and the flash
# (its light); the axes are the original's (forward (0, -0.1177,
# -0.99305), up (0, 0.99305, -0.1177), right +x).
type Cam is Data:
  Cam{ex: F32, ey: F32, ez: F32, focal: F32, hx: F32, hy: F32, hz: F32,
    flash: F32}

# A world point on the screen as (x, y, 1 / depth); w = 0 is behind the
# eye. The original projected a 1024 x 640 frame about (512, 310).
def Cam.proj(+cam: Cam, +p: Vec) -> Vec:
  Cam{ex, ey, ez, focal, _, _, _, _} = cam
  Vec{px, py, pz} = p
  +rx = (px - ex : F32)
  +ry = (py - ey : F32)
  +rz = (pz - ez : F32)
  +depth = (0.0 - 0.1177 * ry - 0.99305 * rz : F32)
  +w = Math.pick((depth > 0.5 : F32), (1.0 / depth : F32), 0.0)
  Vec{(960.0 + focal * rx * w : F32),
    (581.25 - focal * (0.99305 * ry - 0.1177 * rz) * w : F32), w}

# The pixels a world unit spans at p (the focal length over the depth).
def Cam.px(+cam: Cam, +p: Vec) -> F32:
  Cam{_, _, _, focal, _, _, _, _} = cam
  Vec.dot(Cam.proj(cam, p), Vec{0.0, 0.0, focal})

# The lens: its target, its width and their speeds.
type Lens is Data:
  Lens{x: F32, y: F32, w: F32, vx: F32, vy: F32, vw: F32}

# The lens a tick later: it leads the hero's fall, frames him and the
# boss, and springs to the frame.
def Lens.follow(
  +l: Lens, +px: F32, +py: F32, +hvx: F32, +hvy: F32, +bx: F32, +by: F32,
  +byaw: F32
) -> Lens:
  Lens{x, y, w, vx, vy, vw} = l
  +cx = Math.clamp((px * 0.55 + (bx - F32.cos(byaw)) * 0.45 : F32),
    (0.0 - 5.0 : F32), 5.0)
  +lead = (hvy * 3.0 : F32)
  +low = Math.min((py + lead : F32), by)
  +high = Math.max((py + 1.8 + lead : F32), (by + 5.1 : F32))
  +wide = Math.clamp(Math.max((F32.abs((px - bx : F32)) + 14.0 : F32),
      ((high - low + 2.2) * 2.0 : F32)), 19.0, 39.0)
  +cy = Math.clamp(((low + high) * 0.5 - wide * 0.055 : F32), (0.0 - 4.5 : F32),
    8.0)
  +dx = Math.clamp(((vx + (cx - x) * 0.06) * 0.68 : F32), (0.0 - 0.25 : F32), 0.25)
  +dy = Math.clamp(((vy + (cy - y) * 0.06) * 0.68 : F32), (0.0 - 0.20 : F32), 0.20)
  +dw = ((vw + (wide - w) * 0.035) * 0.72 : F32)
  Lens{(x + dx : F32), (y + dy : F32), (w + dw : F32), dx, dy, dw}

# The camera of a lens at a time: the eye 3.2 over and 27 before the
# target, shaken by the flash.
def Cam.at(+l: Lens, +t: F32, +flash: U32, +hit: Vec) -> Cam:
  Lens{x, y, w, _, _, _} = l
  Vec{hx, hy, hz} = hit
  +shake = (U32.to_f32(flash) * 0.011 : F32)
  Cam{(x + F32.sin((t * 2.4 : F32)) * shake : F32),
    (y + 3.2 + F32.cos((t * 2.9 : F32)) * shake * 0.6 : F32), 27.0,
    (51840.0 / w : F32), hx, hy, hz, U32.to_f32(flash)}

# Surfaces
# --------

# The unit shapes, a point for every (u, v) in the unit square with du
# x dv outward: the sphere; the open cylinder from y = 0 to 1; the horn
# and the blade (tapered, curving in +x, root at y = 0); the sides of
# the box [-1, 1]^3 (corners at u = 0, 1/4, 1/2, 3/4); its lid at y =
# 1; the octahedron.
type Shape is Data:
  Globe{}
  Tube{}
  Horn{}
  Blade{}
  Box{}
  Plate{}
  Gem{}

# A surface: a unit shape in a basis (origin, three axes); a cloth
# sheet, Catmull-Rom over its top row a..d and bottom row e..h; a ring
# at height cy of radius r0..r1 on the ellipse (sx, sz); the cliff
# under the arena; the arch over x at z = -15.
type Surf is Data:
  Inst{k: Shape, ox: F32, oy: F32, oz: F32, xx: F32, xy: F32, xz: F32, yx: F32,
    yy: F32, yz: F32, zx: F32, zy: F32, zz: F32}
  Sheet{ax: F32, ay: F32, az: F32, bx: F32, by: F32, bz: F32, cx: F32, cy: F32,
    cz: F32, dx: F32, dy: F32, dz: F32, ex: F32, ey: F32, ez: F32, fx: F32,
    fy: F32, fz: F32, gx: F32, gy: F32, gz: F32, hx: F32, hy: F32, hz: F32}
  Ring{cx: F32, cy: F32, cz: F32, sx: F32, sz: F32, r0: F32, r1: F32}
  Cliff{}
  Arch{x: F32}

def Unit.go(k: Shape, +u: F32, +v: F32, +a: F32, +b: F32, +w: F32) -> Vec:
  match k:
    case Globe{}:
      +sb = F32.sin(b)
      Vec{(F32.cos(a) * sb : F32), F32.cos(b), (F32.sin(a) * sb : F32)}
    case Tube{}:
      Vec{F32.cos(a), w, F32.sin(a)}
    case Horn{}:
      +r = (v * 0.18 : F32)
      Vec{(w * w * 0.45 + r * F32.cos(a) : F32), w, (r * F32.sin(a) : F32)}
    case Blade{}:
      +tip = (1.0 - w * 0.985 : F32)
      Vec{(w * w * 0.2 + 0.064 * tip * F32.cos(a) : F32), w,
        (0.012 * tip * F32.sin(a) : F32)}
    case Box{}:
      +ca = F32.cos((a + 0.7853982 : F32))
      +sa = F32.sin((a + 0.7853982 : F32))
      +m = (1.0 / Math.max(F32.abs(ca), F32.abs(sa)) : F32)
      Vec{(ca * m : F32), (1.0 - 2.0 * v : F32), (sa * m : F32)}
    case Plate{}:
      Vec{(2.0 * u - 1.0 : F32), 1.0, (1.0 - 2.0 * v : F32)}
    case Gem{}:
      +sb = F32.sin(b)
      +x = (F32.cos(a) * sb : F32)
      +y = F32.cos(b)
      +z = (F32.sin(a) * sb : F32)
      +d = (1.0 / (F32.abs(x) + F32.abs(y) + F32.abs(z) : F32) : F32)
      Vec{(x * d : F32), (y * d : F32), (z * d : F32)}

def Unit.at(k: Shape, +u: F32, +v: F32) -> Vec:
  Unit.go(k, u, v, (6.2831853 * u : F32), (3.1415927 * v : F32), (1.0 - v : F32))

def Inst.map(
  +p: Vec, +ox: F32, +oy: F32, +oz: F32, +xx: F32, +xy: F32, +xz: F32, +yx: F32,
  +yy: F32, +yz: F32, +zx: F32, +zy: F32, +zz: F32
) -> Vec:
  Vec{px, py, pz} = p
  Vec{(ox + xx * px + yx * py + zx * pz : F32),
    (oy + xy * px + yy * py + zy * pz : F32),
    (oz + xz * px + yz * py + zz * pz : F32)}

# Catmull-Rom through b and c, steered by a and d.
def Spline.at(+a: F32, +b: F32, +c: F32, +d: F32, +u: F32) -> F32:
  (0.5 * (2.0 * b + (c - a) * u + (2.0 * a - 5.0 * b + 4.0 * c - d) * u * u
    + (3.0 * b - a + d - 3.0 * c) * u * u * u) : F32)

def Arch.x(+x: F32, +u: F32) -> F32:
  (x - F32.cos((3.1415927 * u : F32)) * 3.1 : F32)

# The vault over the columns: a half ellipse 3.1 wide and 4.0 high.
def Arch.y(+u: F32) -> F32:
  (4.3 + 4.0 * F32.sin((3.1415927 * u : F32)) : F32)

def Surf.at(+s: Surf, +u: F32, +v: F32) -> Vec:
  match s:
    case Inst{k, ox, oy, oz, xx, xy, xz, yx, yy, yz, zx, zy, zz}:
      Inst.map(Unit.at(k, u, v), ox, oy, oz, xx, xy, xz, yx, yy, yz, zx, zy, zz)
    case Sheet{ax, ay, az, bx, by, bz, cx, cy, cz, dx, dy, dz, ex, ey, ez, fx, fy,
        fz, gx, gy, gz, hx, hy, hz}:
      Vec.mix(Vec{Spline.at(ax, bx, cx, dx, u), Spline.at(ay, by, cy, dy, u),
          Spline.at(az, bz, cz, dz, u)},
        Vec{Spline.at(ex, fx, gx, hx, u), Spline.at(ey, fy, gy, hy, u),
          Spline.at(ez, fz, gz, hz, u)}, v)
    case Ring{cx, cy, cz, sx, sz, r0, r1}:
      +a = (6.2831853 * u : F32)
      +r = (r0 + (r1 - r0) * v : F32)
      Vec{(cx + sx * r * F32.cos(a) : F32), cy, (cz + sz * r * F32.sin(a) : F32)}
    case Cliff{}:
      +a = (6.2831853 * u : F32)
      +brk = (F32.sin((7.0 * a : F32)) * 0.15 + F32.cos((13.0 * a : F32)) * 0.08 : F32)
      +r = ((1.0 - v * 0.66 - v * v * v * v * 0.34)
        * (1.0 + brk * Math.min(1.0, (v * 6.0 : F32))) : F32)
      Vec{(F32.cos(a) * r * 7.3 : F32),
        (0.0 - v * 3.55 - brk * F32.sin((3.1415927 * v : F32)) * 0.7 : F32),
        (F32.sin(a) * r * 3.5 : F32)}
    case Arch{x}:
      +px = Arch.x(x, u)
      +py = Arch.y(u)
      +tx = (Arch.x(x, (u + 0.002 : F32)) - px : F32)
      +ty = (Arch.y((u + 0.002 : F32)) - py : F32)
      +il = (0.19 / Math.max(0.00001, F32.sqrt((tx * tx + ty * ty : F32))) : F32)
      +ca = F32.cos((0.7853982 - 6.2831853 * v : F32))
      +sa = F32.sin((0.7853982 - 6.2831853 * v : F32))
      +m = (1.0 / Math.max(F32.abs(ca), F32.abs(sa)) : F32)
      Vec{(px - ty * il * ca * m : F32), (py + tx * il * ca * m : F32),
        (0.19 * sa * m - 15.0 : F32)}

# A unit shape scaled at a centre; in a basis; from a to b (its y), w
# wide across and d deep.
def Inst.ball(k: Shape, +c: Vec, +sx: F32, +sy: F32, +sz: F32) -> Surf:
  Vec{cx, cy, cz} = c
  Inst{k, cx, cy, cz, sx, 0.0, 0.0, 0.0, sy, 0.0, 0.0, 0.0, sz}

def Inst.of(k: Shape, +a: Vec, +x: Vec, +y: Vec, +z: Vec) -> Surf:
  Vec{ax, ay, az} = a
  Vec{xx, xy, xz} = x
  Vec{yx, yy, yz} = y
  Vec{zx, zy, zz} = z
  Inst{k, ax, ay, az, xx, xy, xz, yx, yy, yz, zx, zy, zz}

def Inst.span(k: Shape, +a: Vec, +b: Vec, +w: F32, +d: F32) -> Surf:
  +axis = Vec.sub(b, a)
  +up = Vec.unit(axis)
  +right = Vec.unit(Vec.cross(up, Vec{0.002, 0.0, 1.0}))
  Inst.of(k, a, Vec.scale(right, w), axis, Vec.scale(Vec.unit(Vec.cross(right, up)), d))

# An instance turned about y by face and moved to p; other surfaces
# stay.
def Surf.turn(+s: Surf, +p: Vec, +face: F32) -> Surf:
  match s:
    case Inst{k, ox, oy, oz, xx, xy, xz, yx, yy, yz, zx, zy, zz}:
      Vec{px, py, pz} = p
      +c = F32.cos(face)
      +sn = F32.sin(face)
      Inst{k, (px + ox * c + oz * sn : F32), (py + oy : F32),
        (pz + oz * c - ox * sn : F32), (xx * c + xz * sn : F32), xy,
        (xz * c - xx * sn : F32), (yx * c + yz * sn : F32), yy,
        (yz * c - yx * sn : F32), (zx * c + zz * sn : F32), zy,
        (zz * c - zx * sn : F32)}
    case other:
      other

# Light
# -----

# A material: tint, roughness, metalness, glow, grain (the stone's or
# the moon's mottle), blend mode (0 opaque, 1 alpha, 2 additive), alpha.
type Grain is Data:
  Plain{}
  Stone{}
  Moon{}

type Mat is Data:
  Mat{c: U32, rough: F32, metal: F32, glow: F32, grain: Grain, m: U32, al: F32}

# The original's plain face (roughness 0.62), a painted part, a bead, a
# bone, a translucent face.
def Mat.flat(+c: U32) -> Mat:
  Mat{c, 0.62, 0.0, 0.0, Plain{}, 0, 1.0}

def Mat.paint(+c: U32, +rough: F32, +metal: F32, +glow: F32) -> Mat:
  Mat{c, rough, metal, glow, Plain{}, 0, 1.0}

def Mat.bead(+c: U32, +glow: F32) -> Mat:
  Mat.paint(c, 0.24, 0.20, glow)

def Mat.bone(+c: U32) -> Mat:
  Mat.paint(c, 0.38, 0.30, 0.0)

def Mat.alpha(+c: U32, +al: F32) -> Mat:
  Mat{c, 1.0, 0.0, 0.0, Plain{}, 1, al}

# The tint at a point: the colour, or the stone's faint grain from the
# place (2239030 toward 7765633) or the moon's from (u, v) (7774082 to
# 14213066).
def Mat.tint(grain: Grain, +c: U32, +p: Vec, +u: F32, +v: F32) -> Vec:
  match grain:
    case Plain{}:
      Vec.rgb(c)
    case Stone{}:
      Vec{x, y, z} = p
      +g = (F32.sin((x * 2.4 + z * 3.1 : F32)) * F32.cos((y * 2.3 - z * 1.7 : F32)) : F32)
      Vec.mix(Vec.rgb(2239030), Vec.rgb(7765633), (0.3 * Math.sat((0.36 + g * 0.14
        + F32.sin((x * 7.8 + y * 3.2 + z * 5.4 : F32)) * 0.06 : F32)) : F32))
    case Moon{}:
      +g = (F32.sin((v * 34.0 + F32.sin((u * 41.0 : F32)) * 2.0 : F32))
        * F32.cos((u * 47.0 + F32.sin((v * 28.0 : F32)) : F32)) : F32)
      Vec.mix(Vec.rgb(7774082), Vec.rgb(14213066), (0.52 + 0.18 * g * g : F32))

# ACES on a linear channel, then gamma.
def Light.tone(+x: F32) -> F32:
  F32.pow(Math.sat(((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14) : F32)),
    0.4545)

def Light.tone3(+c: Vec) -> Vec:
  Vec{r, g, b} = c
  Vec{Light.tone(r), Light.tone(g), Light.tone(b)}

def Light.gamma(+c: Vec) -> Vec:
  Vec{r, g, b} = c
  Vec{F32.pow(r, 2.2), F32.pow(g, 2.2), F32.pow(b, 2.2)}

# A channel of one light: Schlick's Fresnel f over f0, Lambert of the
# rest, the specular sp.
def Light.ch(+base: F32, +f0: F32, +fr: F32, +sp: F32, +kd: F32, +lc: F32, +nl: F32) -> F32:
  +f = (f0 + (1.0 - f0) * fr : F32)
  (((1.0 - f) * kd * base + sp * f) * lc * nl : F32)

# One light of colour lc (intensity and attenuation in) from the
# direction l on a point of normal n seen along v: GGX (a2), Smith (k).
def Light.one(
  +base: Vec, +f0: Vec, +n: Vec, +v: Vec, +l: Vec, +nv: F32, +a2: F32, +k: F32,
  +kd: F32, +lc: Vec
) -> Vec:
  Vec{br, bg, bb} = base
  Vec{fr0, fg0, fb0} = f0
  Vec{lr, lg, lb} = lc
  +nl = Math.max(0.0, Vec.dot(n, l))
  +h = Vec.unit(Vec.add(v, l))
  +nh = Math.max(0.0, Vec.dot(n, h))
  +vh = Math.max(0.0, Vec.dot(v, h))
  +den = (nh * nh * (a2 - 1.0) + 1.0 : F32)
  +d = (a2 / Math.max(0.00001, (3.1415927 * den * den : F32)) : F32)
  +g = ((nv / (nv * (1.0 - k) + k)) * (nl / (nl * (1.0 - k) + k)) : F32)
  +t = (1.0 - vh : F32)
  +fr = (t * t * t * t * t : F32)
  +sp = (d * g / Math.max(0.0001, (4.0 * nv * nl : F32)) : F32)
  Vec{Light.ch(br, fr0, fr, sp, kd, lr, nl), Light.ch(bg, fg0, fr, sp, kd, lg, nl),
    Light.ch(bb, fb0, fr, sp, kd, lb, nl)}

# A point light at q of range: the direction and the attenuation.
def Light.pt(
  +base: Vec, +f0: Vec, +n: Vec, +v: Vec, +p: Vec, +q: Vec, +nv: F32, +a2: F32,
  +k: F32, +kd: F32, +lc: Vec, +range: F32
) -> Vec:
  +delta = Vec.sub(q, p)
  +d = F32.sqrt(Vec.dot(delta, delta))
  +near = Math.sat((1.0 - d / range : F32))
  Light.one(base, f0, n, v, Vec.scale(delta, (1.0 / Math.max(0.001, d) : F32)), nv,
    a2, k, kd, Vec.scale(lc, (near * near / (1.0 + 0.08 * d * d : F32) : F32)))

# The normal facing the viewer.
def Light.face(+n: Vec, +v: Vec) -> Vec:
  Vec.scale(n, Math.pick((Vec.dot(n, v) < 0.0 : F32), (0.0 - 1.0 : F32), 1.0))

def Light.sum(+base: Vec, +tint: Vec, +glow: F32, +a: Vec, +b: Vec, +c: Vec, +d: Vec) -> Vec:
  Vec{br, bg, bb} = base
  Light.tone3(Vec.add(Vec.add(Vec{(br * 0.1412 : F32), (bg * 0.1725 : F32), (bb * 0.2588 : F32)},
      Vec.scale(tint, glow)), Vec.add(Vec.add(a, b), Vec.add(c, d))))

# The colour of a point p of normal n under the original's lights: the
# ambient (36, 44, 66); the suns (-0.4, -0.8, -0.6) at (185, 213, 255)
# x 3.4 and (0.5, -0.3, 0.7) at (128, 163, 255) x 2.5; the point (-5,
# 3, 4) at (255, 172, 104) x 5 over 18; the contact light (150, 244,
# 255) x 12 in a flash, else 0.2, over 8; the glow.
def Light.at(+mat: Mat, +p: Vec, +n: Vec, +u: F32, +v: F32, +cam: Cam) -> Vec:
  Mat{c, rough, metal, glow, grain, _, _} = mat
  Cam{ex, ey, ez, _, hx, hy, hz, flash} = cam
  +tint = Mat.tint(grain, c, p, u, v)
  +base = Light.gamma(tint)
  +view = Vec.unit(Vec.sub(Vec{ex, ey, ez}, p))
  +nn = Light.face(Vec.unit(n), view)
  +nv = Math.max(0.0001, Vec.dot(nn, view))
  +r = Math.clamp(rough, 0.06, 1.0)
  +a2 = (r * r * r * r : F32)
  +k = ((r + 1.0) * (r + 1.0) * 0.125 : F32)
  +kd = ((1.0 - metal) * 0.3183099 : F32)
  +f0 = Vec.mix(Vec{0.04, 0.04, 0.04}, base, metal)
  Light.sum(base, tint, glow,
    Light.one(base, f0, nn, view, Vec{0.3714, 0.7428, 0.5571}, nv, a2, k, kd,
      Vec{2.4667, 2.84, 3.4}),
    Light.one(base, f0, nn, view, Vec{(0.0 - 0.5488 : F32), 0.3293, (0.0 - 0.7683 : F32)},
      nv, a2, k, kd, Vec{1.2549, 1.598, 2.5}),
    Light.pt(base, f0, nn, view, p, Vec{(0.0 - 5.0 : F32), 3.0, 4.0}, nv, a2, k, kd,
      Vec{5.0, 3.3725, 2.0392}, 18.0),
    Light.pt(base, f0, nn, view, p, Vec{hx, hy, (hz + 0.7 : F32)}, nv, a2, k, kd,
      Vec.scale(Vec{0.5882, 0.9569, 1.0}, Math.pick((flash > 0.0 : F32), 12.0, 0.2)),
      8.0))

# Triangles
# ---------

# A vertex on the screen (x, y, 1 / depth) with its colour.
type Vert is Data:
  Vert{x: F32, y: F32, w: F32, r: F32, g: F32, b: F32}

# A screen triangle: two barycentric planes (l0 = a0 x + b0 y + c0, l1
# likewise, l2 = 1 - l0 - l1: inside when none is negative), the
# inverse-depth plane (the nearest has the largest w), the three colour
# planes, its mode (0 opaque, 1 alpha, 2 additive, 3 soft: a shadow
# whose r and g planes hold its ground coordinates times w) and alpha,
# and its pixel box.
type Tri is Data:
  Tri{a0: F32, b0: F32, c0: F32, a1: F32, b1: F32, c1: F32, wc: F32, wu: F32,
    wv: F32, rc: F32, ru: F32, rv: F32, gc: F32, gu: F32, gv: F32, bc: F32,
    bu: F32, bv: F32, m: U32, al: F32, x0: U32, y0: U32, x1: U32, y1: U32}

# A cons list: the one shape a flat loop walks with no stack.
type Tris is Data:
  TNil{}
  TCons{+tri: Tri, next: Tris}

# The triangles by 64-cell: a quadtree over the 2048 root whose leaves
# are the cells' lists with their counts; an empty region is one node.
type Cells is Data:
  CNil{}
  CLeaf{+n: U32, +ts: Tris}
  CQua{tl: Cells, tr: Cells, bl: Cells, br: Cells}

# a reversed onto b (the order of a list does not matter).
def Tris.app(a: Tris, b: Tris) -> Tris:
  match a:
    case TNil{}:
      b
    case TCons{t, n}:
      Tris.app(n, TCons{t, b})

# The extremes of a plane over the box's corners.
def Tri.wmax(
  +wc: F32, +wx: F32, +wy: F32, +fx0: F32, +fy0: F32, +fx1: F32, +fy1: F32
) -> F32:
  Math.max(Math.max((wc + wx * fx0 + wy * fy0 : F32),
      (wc + wx * fx1 + wy * fy0 : F32)),
    Math.max((wc + wx * fx0 + wy * fy1 : F32), (wc + wx * fx1 + wy * fy1 : F32)))

# Are the box's corner pixels not separated from the triangle by an
# edge (s = 1), or all inside every edge (s = -1: the least, as the
# negated greatest)?
def Tri.cover(
  +s: F32, +t: Tri, +fx0: F32, +fy0: F32, +fx1: F32, +fy1: F32
) -> Bool:
  Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
    m, al, x0, y0, x1, y1} = t
  ((s * Tri.wmax((s * c0 : F32), (s * a0 : F32), (s * b0 : F32), fx0, fy0, fx1,
      fy1) >= 0.0)
    && (s * Tri.wmax((s * c1 : F32), (s * a1 : F32), (s * b1 : F32), fx0, fy0, fx1,
      fy1) >= 0.0)
    && (s * Tri.wmax((s * (1.0 - c0 - c1) : F32), (0.0 - s * (a0 + a1) : F32),
      (0.0 - s * (b0 + b1) : F32), fx0, fy0, fx1, fy1) >= 0.0) : F32)

# Cells
# -----

def Cells.add(c: Cells, +t: Tri) -> Cells:
  match c:
    case CLeaf{n, ts}:
      CLeaf{(n + 1 : U32), TCons{t, ts}}
    case _:
      CLeaf{1, TCons{t, TNil{}}}

# Bit 4: the quadrant of a coordinate shifted so its level's bit sits
# there.
def Cells.bit(+c: U32) -> Bool:
  ((c .&. 16) > 0 : U32)

# The triangle put in the cell (cx, cy) of a region of 64 << k: right and
# low pick the quadrant at this level, cx and cy are shifted for the
# next.
def Cells.put(
  k: Nat, right: Bool, low: Bool, c: Cells, +cx: U32, +cy: U32, +t: Tri
) -> Cells:
  match k:
    case 0n:
      Cells.add(c, t)
    case 1n+e:
      match right low c:
        case False{} False{} CQua{tl, tr, bl, br}:
          CQua{Cells.put(e, Cells.bit(cx), Cells.bit(cy), tl, (cx << 1n : U32),
            (cy << 1n : U32), t), tr, bl, br}
        case True{} False{} CQua{tl, tr, bl, br}:
          CQua{tl, Cells.put(e, Cells.bit(cx), Cells.bit(cy), tr, (cx << 1n : U32),
            (cy << 1n : U32), t), bl, br}
        case False{} True{} CQua{tl, tr, bl, br}:
          CQua{tl, tr, Cells.put(e, Cells.bit(cx), Cells.bit(cy), bl, (cx << 1n : U32),
            (cy << 1n : U32), t), br}
        case True{} True{} CQua{tl, tr, bl, br}:
          CQua{tl, tr, bl, Cells.put(e, Cells.bit(cx), Cells.bit(cy), br,
            (cx << 1n : U32), (cy << 1n : U32), t)}
        case False{} False{} _:
          CQua{Cells.put(e, Cells.bit(cx), Cells.bit(cy), CNil{}, (cx << 1n : U32),
            (cy << 1n : U32), t), CNil{}, CNil{}, CNil{}}
        case True{} False{} _:
          CQua{CNil{}, Cells.put(e, Cells.bit(cx), Cells.bit(cy), CNil{},
            (cx << 1n : U32), (cy << 1n : U32), t), CNil{}, CNil{}}
        case False{} True{} _:
          CQua{CNil{}, CNil{}, Cells.put(e, Cells.bit(cx), Cells.bit(cy), CNil{},
            (cx << 1n : U32), (cy << 1n : U32), t), CNil{}}
        case True{} True{} _:
          CQua{CNil{}, CNil{}, CNil{}, Cells.put(e, Cells.bit(cx), Cells.bit(cy),
            CNil{}, (cx << 1n : U32), (cy << 1n : U32), t)}

# Two trees of the same region as one.
def Cells.merge(a: Cells, b: Cells) -> Cells:
  match a b:
    case CNil{} _:
      b
    case CLeaf{n, ts} CNil{}:
      CLeaf{n, ts}
    case CLeaf{n, ts} CLeaf{m, us}:
      CLeaf{(n + m : U32), Tris.app(ts, us)}
    case CQua{a1, a2, a3, a4} CNil{}:
      CQua{a1, a2, a3, a4}
    case CQua{a1, a2, a3, a4} CQua{b1, b2, b3, b4}:
      CQua{Cells.merge(a1, b1), Cells.merge(a2, b2), Cells.merge(a3, b3),
        Cells.merge(a4, b4)}
    case _ _:
      CNil{}

# Does the triangle meet the pixel centres of the cell?
def Tri.meets(+t: Tri, +cx: U32, +cy: U32) -> Bool:
  +fx0 = (U32.to_f32((cx << 6n : U32)) + 0.5 : F32)
  +fy0 = (U32.to_f32((cy << 6n : U32)) + 0.5 : F32)
  Tri.cover(1.0, t, fx0, fy0, (fx0 + 63.0 : F32), (fy0 + 63.0 : F32))

def Tri.into(hit: Bool, +cx: U32, +cy: U32, +t: Tri, c: Cells) -> Cells:
  match hit:
    case False{}:
      c
    case True{}:
      Cells.put(5n, Cells.bit(cx), Cells.bit(cy), c, (cx << 1n : U32),
        (cy << 1n : U32), t)

# The triangle put in the cells of its box that it meets: m cells left
# of w columns from (cx0, cy0).
def Tri.spread(+m: Nat, +w: U32, +cx0: U32, +cy0: U32, +t: Tri, c: Cells) -> Cells:
  match m:
    case 0n:
      c
    case 1n+p:
      +i = U32.from_nat(p)
      +cx = (cx0 + i % w : U32)
      +cy = (cy0 + i / w : U32)
      Tri.spread(p, w, cx0, cy0, t, Tri.into(Tri.meets(t, cx, cy), cx, cy, t, c))


# Meshing
# -------

def Mesh.norm(+a: Vec, +b: Vec, +c: Vec, +d: Vec) -> Vec:
  Vec{ax, ay, az} = a
  Vec{bx, by, bz} = b
  Vec{cx, cy, cz} = c
  Vec{dx, dy, dz} = d
  +ux = (ax - bx : F32)
  +uy = (ay - by : F32)
  +uz = (az - bz : F32)
  +vx = (cx - dx : F32)
  +vy = (cy - dy : F32)
  +vz = (cz - dz : F32)
  Vec{(uy * vz - uz * vy : F32), (uz * vx - ux * vz : F32),
    (ux * vy - uy * vx : F32)}

def Mesh.vert.go(+p: Vec, +l: Vec) -> Vert:
  Vec{x, y, w} = p
  Vec{r, g, b} = l
  Vert{x, y, w, r, g, b}

# The colour lit, or as is (a transparent surface glows).
def Mesh.shade(
  lit: Bool, +mat: Mat, +p: Vec, +n: Vec, +u: F32, +v: F32, +cam: Cam
) -> Vec:
  match lit:
    case True{}:
      Light.at(mat, p, n, u, v, cam)
    case False{}:
      Mat{c, _, _, _, _, _, _} = mat
      Vec.rgb(c)

# The vertex at (u, v): its projection and its colour under the normal
# by forward differences (the same stencil on every patch that shares
# the vertex, so the shading is seamless; v kept off the poles, where
# the stencil collapses).
def Mesh.vert(+s: Surf, +mat: Mat, +u: F32, +v: F32, +cam: Cam) -> Vert:
  Mat{_, _, _, _, _, m, _} = mat
  +p = Surf.at(s, u, v)
  +vn = Math.clamp(v, 0.0025, 0.9975)
  +q = Surf.at(s, u, vn)
  Mesh.vert.go(Cam.proj(cam, p), Mesh.shade(U32.is_eq(m, 0), mat, p, Mesh.norm(
    Surf.at(s, (u + 0.005 : F32), vn), q, Surf.at(s, u, (vn + 0.005 : F32)), q), u,
    v, cam))

def Tri.plane(
  +a0: F32, +b0: F32, +c0: F32, +a1: F32, +b1: F32, +c1: F32, +v0: F32,
  +v1: F32, +v2: F32
) -> Vec:
  +d0 = (v0 - v2 : F32)
  +d1 = (v1 - v2 : F32)
  Vec{(v2 + c0 * d0 + c1 * d1 : F32), (a0 * d0 + a1 * d1 : F32),
    (b0 * d0 + b1 * d1 : F32)}

# The triangle of its planes and pixel box put in the cells its box
# spans.
def Mesh.tri(
  +a0: F32, +b0: F32, +c0: F32, +a1: F32, +b1: F32, +c1: F32, +w: Vec, +r: Vec,
  +g: Vec, +b: Vec, +m: U32, +al: F32, +x0: U32, +y0: U32, +x1: U32, +y1: U32,
  c: Cells
) -> Cells:
  Vec{wc, wu, wv} = w
  Vec{rc, ru, rv} = r
  Vec{gc, gu, gv} = g
  Vec{bc, bu, bv} = b
  +cx0 = (x0 >> 6n : U32)
  +cy0 = (y0 >> 6n : U32)
  +cw = ((x1 >> 6n) - cx0 + 1 : U32)
  Tri.spread(U32.to_nat((cw * ((y1 >> 6n) - cy0 + 1) : U32)), cw, cx0, cy0,
    Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
      m, al, x0, y0, x1, y1}, c)

def Mesh.keep(
  ok: Bool, +p: Vert, +q: Vert, +r: Vert, +area: F32, +m: U32, +al: F32,
  +bx0: F32, +by0: F32, +bx1: F32, +by1: F32, c: Cells
) -> Cells:
  match ok:
    case False{}:
      c
    case True{}:
      Vert{x0, y0, w0, cr0, cg0, cb0} = p
      Vert{x1, y1, w1, cr1, cg1, cb1} = q
      Vert{x2, y2, w2, cr2, cg2, cb2} = r
      +ia = (1.0 / area : F32)
      +a0 = ((y1 - y2) * ia : F32)
      +b0 = ((x2 - x1) * ia : F32)
      +c0 = (0.0 - (a0 * x2 + b0 * y2) : F32)
      +a1 = ((y2 - y0) * ia : F32)
      +b1 = ((x0 - x2) * ia : F32)
      +c1 = (0.0 - (a1 * x2 + b1 * y2) : F32)
      Mesh.tri(a0, b0, c0, a1, b1, c1,
        Tri.plane(a0, b0, c0, a1, b1, c1, w0, w1, w2),
        Tri.plane(a0, b0, c0, a1, b1, c1, cr0, cr1, cr2),
        Tri.plane(a0, b0, c0, a1, b1, c1, cg0, cg1, cg2),
        Tri.plane(a0, b0, c0, a1, b1, c1, cb0, cb1, cb2), m, al, F32.to_u32(bx0),
        F32.to_u32(by0), F32.to_u32(bx1), F32.to_u32(by1), c)

# Three vertices into the cells, or nothing when one is behind the eye,
# the box misses the screen, or an opaque one faces away (its screen
# area is not negative: the surfaces wind outward).
def Mesh.raster(+p: Vert, +q: Vert, +r: Vert, +m: U32, +al: F32, c: Cells) -> Cells:
  Vert{x0, y0, w0, _, _, _} = p
  Vert{x1, y1, w1, _, _, _} = q
  Vert{x2, y2, w2, _, _, _} = r
  +area = ((y1 - y2) * (x0 - x2) + (x2 - x1) * (y0 - y2) : F32)
  +bx0 = Math.max(0.0, F32.floor(Math.min(x0, Math.min(x1, x2))))
  +by0 = Math.max(0.0, F32.floor(Math.min(y0, Math.min(y1, y2))))
  +bx1 = Math.min(1919.0, F32.ceil(Math.max(x0, Math.max(x1, x2))))
  +by1 = Math.min(1199.0, F32.ceil(Math.max(y0, Math.max(y1, y2))))
  Mesh.keep(Bool.and(((w0 > 0.0) && (w1 > 0.0) && (w2 > 0.0) && (bx0 <= bx1)
      && (by0 <= by1) && (F32.abs(area) > 0.001) : F32),
      Bool.or((area < 0.0 : F32), (m > 0 : U32))), p, q, r, area, m, al, bx0,
    by0, bx1, by1, c)

# A patch (p, q over r, t) as two triangles.
def Grid.patch(
  +p: Vert, +q: Vert, +r: Vert, +t: Vert, +m: U32, +al: F32, c: Cells
) -> Cells:
  Mesh.raster(p, t, r, m, al, Mesh.raster(p, q, t, m, al, c))

# The strip [u0, u1] of a grid: j patches left below v, whose top corners
# are p (at u0) and q (at u1).
def Grid.strip(
  j: Nat, +s: Surf, +mat: Mat, +cam: Cam, +u0: F32, +u1: F32, +v: F32, +dv: F32,
  +p: Vert, +q: Vert, acc: Cells
) -> Cells:
  match j:
    case 0n:
      acc
    case 1n+k:
      Mat{_, _, _, _, _, m, al} = mat
      +v1 = (v + dv : F32)
      +r = Mesh.vert(s, mat, u0, v1, cam)
      +t = Mesh.vert(s, mat, u1, v1, cam)
      Grid.strip(k, s, mat, cam, u0, u1, v1, dv, r, t,
        Grid.patch(p, q, r, t, m, al, acc))

# The strips [i, i + 2^d) of a grid of nu by nv patches, a fork tree; a
# strip past the last is nothing.
def Grid.go(
  +d: Nat, on: Bool, +i: U32, +nu: U32, +nv: U32, +s: Surf, +mat: Mat, +cam: Cam
) -> Cells:
  match d on:
    case 0n True{}:
      +u0 = (U32.to_f32(i) / U32.to_f32(nu) : F32)
      +u1 = (U32.to_f32((i + 1 : U32)) / U32.to_f32(nu) : F32)
      Grid.strip(U32.to_nat(nv), s, mat, cam, u0, u1, 0.0,
        (1.0 / U32.to_f32(nv) : F32), Mesh.vert(s, mat, u0, 0.0, cam),
        Mesh.vert(s, mat, u1, 0.0, cam), CNil{})
    case 1n+e True{}:
      +j = (i + U32.shln(1, e) : U32)
      a b = Grid.go(e, True{}, i, nu, nv, s, mat, cam)
        Grid.go(e, (j < nu : U32), j, nu, nv, s, mat, cam)
      Cells.merge(a, b)
    case _ False{}:
      CNil{}

def Grid.deep(more: Bool, d: Nat) -> Nat:
  match more:
    case True{}:
      1n+d
    case False{}:
      d

# The least d with 2^d >= n, on a fuel.
def Grid.depth(f: Nat, +n: U32, +d: Nat) -> Nat:
  match f:
    case 0n:
      d
    case 1n+p:
      Grid.depth(p, n, Grid.deep((U32.shln(1, d) < n : U32), d))

# The segments a circle of a screen radius (px) needs to stay within a
# pixel of round (its sagitta), at least 4; the 20-px steps over a
# length, at least 1.
def Grid.arc(+r: F32) -> F32:
  Math.max(4.0, F32.ceil((3.1415927 * F32.sqrt((r * 0.5 : F32)) : F32)))

def Grid.len(+l: F32) -> F32:
  Math.max(1.0, F32.ceil((l * 0.05 : F32)))

# The patches a unit shape of screen half sizes (fx, fy, fz; r the
# wider of fx and fz) needs around and along: a horn or a blade by its
# section's sagitta and its length; a box four a side (its corners on
# vertices); the rest by their sagitta both ways.
def Unit.fit(k: Shape, +r: F32, +fx: F32, +fy: F32, +fz: F32) -> Vec:
  match k:
    case Horn{}:
      Vec{Grid.arc((r * 0.18 : F32)), Grid.len(fy), 0.0}
    case Blade{}:
      Vec{Grid.arc((r * 0.064 : F32)), Grid.len(fy), 0.0}
    case Box{}:
      Vec{(4.0 * Grid.len((r * 2.0 : F32)) : F32), Grid.len((fy * 2.0 : F32)), 0.0}
    case _:
      Vec{Grid.arc(r), F32.ceil((Grid.arc(Math.max(r, fy)) * 0.5 : F32)), 0.0}

# The patches a surface needs on the screen (around, along); a sheet, a
# ring, the cliff and the arch keep their grids (the stage is sized by
# the 20-px rule already, and the cliff's bumps need their samples).
def Surf.fit(+s: Surf, +cam: Cam) -> Vec:
  match s:
    case Inst{k, ox, oy, oz, xx, xy, xz, yx, yy, yz, zx, zy, zz}:
      +f = Cam.px(cam, Vec{ox, oy, oz})
      +fx = (f * Vec.len(Vec{xx, xy, xz}) : F32)
      +fy = (f * Vec.len(Vec{yx, yy, yz}) : F32)
      +fz = (f * Vec.len(Vec{zx, zy, zz}) : F32)
      Unit.fit(k, Math.max(fx, fz), fx, fy, fz)
    case _:
      Vec{9999.0, 9999.0, 0.0}

def Mesh.fit(+fit: Vec, +s: Surf, +mat: Mat, +nu: U32, +nv: U32, +cam: Cam) -> Cells:
  Vec{fu, fv, _} = fit
  +mu = F32.to_u32(Math.min(U32.to_f32(nu), fu))
  +mv = F32.to_u32(Math.min(U32.to_f32(nv), fv))
  Grid.go(Grid.depth(9n, mu, 0n), True{}, 0, mu, mv, s, mat, cam)

# A surface of a material as a grid of at most nu by nv patches (fewer
# when it is small on the screen), in the cells.
def Mesh.of(+s: Surf, +mat: Mat, +nu: U32, +nv: U32, +cam: Cam) -> Cells:
  Mesh.fit(Surf.fit(s, cam), s, mat, nu, nv, cam)


# A screen quad (its corners in order, counter-clockwise on the screen
# when opaque) at the inverse depth w, of one colour, in the cells.
def Quad.put(
  +x0: F32, +y0: F32, +x1: F32, +y1: F32, +x2: F32, +y2: F32, +x3: F32, +y3: F32,
  +w: F32, +c: U32, +m: U32, +al: F32, cells: Cells
) -> Cells:
  +r = Math.chan(c, 16n)
  +g = Math.chan(c, 8n)
  +b = Math.chan(c, 0n)
  Mesh.raster(Vert{x0, y0, w, r, g, b}, Vert{x2, y2, w, r, g, b},
    Vert{x3, y3, w, r, g, b}, m, al, Mesh.raster(Vert{x0, y0, w, r, g, b},
      Vert{x1, y1, w, r, g, b}, Vert{x2, y2, w, r, g, b}, m, al, cells))


# Stage
# -----

def Cells.m4(a: Cells, b: Cells, c: Cells, d: Cells) -> Cells:
  Cells.merge(Cells.merge(a, b), Cells.merge(c, d))

# A box of half sizes hx, hz from y0 to y1: its sides (nu around) and
# its lid (on top when lid is 1, underneath when -1).
def Box.build(
  +cx: F32, +y0: F32, +y1: F32, +cz: F32, +hx: F32, +hz: F32, +lid: F32, +mat: Mat,
  +nu: U32, +cam: Cam
) -> Cells:
  +hy = ((y1 - y0) * 0.5 : F32)
  +cy = (y0 + hy : F32)
  a b = Mesh.of(Inst{Box{}, cx, cy, cz, hx, 0.0, 0.0, 0.0, hy, 0.0, 0.0, 0.0, hz}, mat,
      nu, 1, cam)
    Mesh.of(Inst{Plate{}, cx, cy, cz, hx, 0.0, 0.0, 0.0, (hy * lid : F32), 0.0, 0.0,
      0.0, (hz * lid : F32)}, mat, 4, 1, cam)
  Cells.merge(a, b)

# A horn strut from under a platform's edge at x to under its centre.
def Stage.strut(+x: F32, +px: F32, +py: F32, +cam: Cam) -> Cells:
  Mesh.of(Inst.span(Horn{}, Vec{x, (py - 0.23 : F32), 0.0}, Vec{px, (py - 0.73 : F32), 0.0},
    0.75, 0.72), Mat.paint(5658961, 0.75, 0.12, 0.0), 8, 4, cam)

# A floating platform of half width r at (px, py): its slab, the
# underside, two struts meeting under it, a glowing bead on its front
# and a bright edge along its top.
def Stage.platform(+px: F32, +py: F32, +r: F32, +cam: Cam) -> Cells:
  a b c d e f = Box.build(px, (py - 0.16 : F32), py, 0.0, r, 0.36, 1.0, Mat.flat(5464411),
      8, cam)
    Box.build(px, (py - 0.25 : F32), (py - 0.17 : F32), 0.0, (r - 0.08 : F32), 0.33,
      (0.0 - 1.0 : F32), Mat.flat(2699574), 8, cam)
    Stage.strut((px - r * 0.72 : F32), px, py, cam) Stage.strut((px + r * 0.72 : F32), px, py, cam)
    Mesh.of(Inst.ball(Globe{}, Vec{px, (py - 0.31 : F32), 0.34}, 0.07, 0.07, 0.028),
      Mat.bead(7395267, 0.9), 8, 4, cam)
    Mesh.of(Inst{Box{}, px, (py + 0.008 : F32), 0.36, 0.0, 0.011, 0.0, (0.0 - r : F32),
      0.0, 0.0, 0.0, 0.0, 0.011}, Mat.paint(11643817, 0.62, 0.0, 0.04), 4, 1, cam)
  Cells.merge(Cells.m4(a, b, c, d), Cells.merge(e, f))

# A column of a ruin at x, from -3 to 4.3 at z = -15.
def Stage.column(+x: F32, +cam: Cam) -> Cells:
  Mesh.of(Inst.span(Tube{}, Vec{x, (0.0 - 3.0 : F32), (0.0 - 15.0 : F32)},
    Vec{x, 4.3, (0.0 - 15.0 : F32)}, 0.24, 0.24), Mat.flat(2239030), 8, 2, cam)

# A ruined arch over x: the round vault, two columns and a low wall
# between them.
def Stage.arch(+x: F32, +cam: Cam) -> Cells:
  a b c d = Mesh.of(Arch{x}, Mat.flat(2239030), 32, 4, cam)
    Stage.column((x - 3.1 : F32), cam) Stage.column((x + 3.1 : F32), cam)
    Box.build(x, (0.0 - 3.1 : F32), (0.0 - 0.9 : F32), (0.0 - 15.0 : F32), 3.0, 0.25, 1.0,
      Mat.flat(1908268), 8, cam)
  Cells.m4(a, b, c, d)

# A lamp of the grove at x (the original's stem at 0.65 at z = -0.8):
# its base, pole, lantern, roof and glowing gem.
def Stage.stem(+x: F32, +cam: Cam) -> Cells:
  +z = (0.0 - 0.8 : F32)
  a b c d e = Box.build(x, 0.0, 0.41, z, 0.065, 0.065, 1.0, Mat.flat(2961983), 4, cam)
    Box.build(x, 0.403, 0.923, z, 0.052, 0.052, 1.0, Mat.flat(5462631), 4, cam)
    Box.build(x, 0.871, 1.079, z, 0.143, 0.143, 1.0, Mat.flat(3356485), 4, cam)
    Mesh.of(Inst.ball(Gem{}, Vec{x, 1.183, z}, 0.234, 0.104, 0.234), Mat.flat(3360328),
      4, 2, cam)
    Mesh.of(Inst.ball(Gem{}, Vec{x, 0.9945, (0.0 - 0.644 : F32)}, 0.065, 0.078, 0.0195),
      Mat.paint(15253430, 0.62, 0.0, 0.7), 4, 2, cam)
  Cells.merge(Cells.m4(a, b, c, d), e)

# The arena's top: the slab (an ellipse of 7.3 x 3.5) and its rim.
def Stage.top(+cam: Cam) -> Cells:
  a b = Mesh.of(Ring{0.0, 0.001, 0.0, 7.3, 3.5, 0.0, 1.0}, Mat.flat(4083018), 64, 2, cam)
    Mesh.of(Ring{0.0, 0.005, 0.0, 7.3, 3.5, 0.986, 0.996}, Mat.flat(9866105), 64, 1, cam)
  Cells.merge(a, b)

# The arena's depths: its inner ring and the cliff beneath.
def Stage.deep(+cam: Cam) -> Cells:
  a b = Mesh.of(Ring{0.0, 0.025, 0.0, 7.3, 3.5, 0.827, 0.83}, Mat.flat(6843496), 64, 1, cam)
    Mesh.of(Cliff{}, Mat{2239030, 0.62, 0.0, 0.0, Stone{}, 0, 1.0}, 64, 12, cam)
  Cells.merge(a, b)

# The middle and right arches.
def Stage.pair(+cam: Cam) -> Cells:
  a b = Stage.arch(0.0, cam) Stage.arch(9.5, cam)
  Cells.merge(a, b)

# The rest of the stage: three platforms, the moon and four lamps.
def Stage.rest(+cam: Cam) -> Cells:
  e f g h i j k l = Stage.platform((0.0 - 4.5 : F32), 2.15, 1.5, cam)
    Stage.platform(4.5, 2.15, 1.5, cam) Stage.platform(0.0, 3.65, 1.55, cam)
    Mesh.of(Inst.ball(Globe{}, Vec{18.0, 9.0, (0.0 - 50.0 : F32)}, 5.0, 5.0, 5.0),
      Mat{7774082, 0.62, 0.0, 0.08, Moon{}, 0, 1.0}, 24, 12, cam)
    Stage.stem(6.4, cam) Stage.stem(5.91, cam) Stage.stem((0.0 - 6.4 : F32), cam)
    Stage.stem((0.0 - 5.91 : F32), cam)
  Cells.merge(Cells.m4(e, f, g, h), Cells.m4(i, j, k, l))

# The ground under (x, y): the top platform, a side one, the arena, or
# none (-100).
def Stage.level(+x: F32, +y: F32) -> F32:
  Math.pick(((F32.abs(x) < 1.55) && (y >= 3.65) : F32), 3.65,
    Math.pick(((F32.abs((F32.abs(x) - 4.5 : F32)) < 1.5) && (y >= 2.15) : F32), 2.15,
      Math.pick(((F32.abs(x) <= 7.3) && (y >= 0.0) : F32), 0.0, (0.0 - 100.0 : F32))))

# A corner of a contact shadow: the ground point q projected, its
# ground coordinates (u, v: the rim at 1) times w in the r and g slots.
def Shadow.vert(+u: F32, +v: F32, +q: Vec) -> Vert:
  Vec{sx, sy, w} = q
  Vert{sx, sy, w, (u * w : F32), (v * w : F32), 0.0}

# The shadow's quad (Tri mode 3): sp by 0.48 sp about x on the ground
# lv, alpha 0.36 at the centre, spread and faded by the height h.
def Shadow.on(on: Bool, +x: F32, +lv: F32, +h: F32, +size: F32, +cam: Cam) -> Cells:
  match on:
    case False{}:
      CNil{}
    case True{}:
      +sp = (size * (1.0 + h * 0.05) : F32)
      +sz = (sp * 0.48 : F32)
      +y = (lv + 0.015 : F32)
      +al = (0.36 / (1.0 + h * 0.30 : F32) : F32)
      +a = Shadow.vert((0.0 - 1.0 : F32), (0.0 - 1.0 : F32),
        Cam.proj(cam, Vec{(x - sp : F32), y, (0.0 - sz : F32)}))
      +b = Shadow.vert(1.0, (0.0 - 1.0 : F32), Cam.proj(cam, Vec{(x + sp : F32), y, (0.0 - sz : F32)}))
      +c = Shadow.vert(1.0, 1.0, Cam.proj(cam, Vec{(x + sp : F32), y, sz}))
      +d = Shadow.vert((0.0 - 1.0 : F32), 1.0, Cam.proj(cam, Vec{(x - sp : F32), y, sz}))
      Mesh.raster(a, c, d, 3, al, Mesh.raster(a, b, c, 3, al, CNil{}))

# The soft shadow of a figure of a size at (x, y); none over the void.
def Shadow.build(+x: F32, +y: F32, +size: F32, +cam: Cam) -> Cells:
  +lv = Stage.level(x, y)
  Shadow.on((lv > (0.0 - 99.0) : F32), x, lv, Math.max(0.0, (y - lv : F32)), size, cam)

# Cloth
# -----

# A cloth: 64 Verlet particles (column i % cols around, row i / cols
# down) in a four-way tree of three levels; a thread is its point and
# its last point. The top row is pinned to its anchor.
type Cloth is Data:
  Thread{p: Vec, old: Vec}
  Weave{a: Cloth, b: Cloth, c: Cloth, d: Cloth}

# A cloth's cut: the columns around (a ring, or open over the back
# half), the rows down, the ring's radius at the top and its growth
# down, the drift back, the top's height over the anchor, the length,
# the flattening in z, the tie across the columns (0 for loose
# strands), the body's radius between lo and hi.
type Fit is Data:
  Fit{cols: U32, rows: U32, open: U32, r0: F32, r1: F32, back: F32, top: F32, len: F32,
    flat: F32, tie: F32, body: F32, lo: F32, hi: F32}

# The hero's cape: a pointed mantle about the shoulders.
def Fit.cape() -> Fit:
  Fit{8, 8, 0, 0.16, 0.36, 0.16, 1.02, 0.78, 0.68, 1.0, 0.13, 0.35, 1.03}

# Particle i at rest about the anchor o, turned to the facing.
def Cloth.rest(+i: U32, +fit: Fit, +o: Vec, +face: F32) -> Vec:
  Fit{cols, rows, open, r0, r1, back, top, len, flat, _, _, _, _} = fit
  +col = U32.to_f32((i % cols : U32))
  +u = Math.pick(U32.is_eq(open, 0), (col * 6.2831853 / U32.to_f32(cols) : F32),
    (1.5707963 + (col + 0.5) * 3.1415927 / U32.to_f32(cols) : F32))
  +v = (U32.to_f32((i / cols : U32)) / U32.to_f32((rows - 1 : U32)) : F32)
  +r = (r0 + v * r1 : F32)
  Vec.add(o, Vec.turn(Vec{(F32.cos(u) * r - v * back : F32),
    (top - v * len * (1.0 + 0.128 * F32.cos((u * 3.0 : F32))) : F32),
    (F32.sin(u) * r * flat : F32)}, face))

# The rest of particle i about o lowered by drop (a crouch).
def Cloth.home(+i: U32, +fit: Fit, +o: Vec, +drop: F32, +face: F32) -> Vec:
  Cloth.rest(i, fit, Vec.sub(o, Vec{0.0, drop, 0.0}), face)

# The particles from i at rest, n levels deep (i, i + s, i + 2s, i + 3s
# for s = 4^n).
def Cloth.seed(+n: Nat, +i: U32, +fit: Fit, +o: Vec, +face: F32) -> Cloth:
  match n:
    case 0n:
      +p = Cloth.rest(i, fit, o, face)
      Thread{p, p}
    case 1n+k:
      +s = U32.shln(1, (k + k : Nat))
      Weave{Cloth.seed(k, i, fit, o, face), Cloth.seed(k, (i + s : U32), fit, o, face),
        Cloth.seed(k, (i + s * 2 : U32), fit, o, face),
        Cloth.seed(k, (i + s * 3 : U32), fit, o, face)}

def Cloth.point(c: Cloth) -> Vec:
  match c:
    case Thread{p, _}:
      p
    case _:
      Vec{0.0, 0.0, 0.0}

# The point of particle i, n levels down (stride 16 at the root).
def Cloth.at(n: Nat, c: Cloth, +i: U32, +stride: U32) -> Vec:
  match n:
    case 0n:
      Cloth.point(c)
    case 1n+k:
      match c:
        case Thread{p, _}:
          p
        case Weave{a, b, cc, d}:
          +part = (i / stride : U32)
          +right = U32.is_ne((part .&. 1 : U32), 0)
          Cloth.at(k, Bool.pick(Cloth, (part >= 2 : U32), Bool.pick(Cloth, right, d, cc),
            Bool.pick(Cloth, right, b, a)), (i % stride : U32), (stride / 4 : U32))

def Cloth.limit(+v: Vec, +m: F32) -> Vec:
  Vec.scale(v, Math.min(1.0, (m / Math.max(0.00001, Vec.len(v)) : F32)))

# Verlet: a thread keeps 0.94 of its motion, falls in a breeze, is
# pulled to its rest and strays only so far from it (the caps and the
# breeze scale with the length); the top row sits at rest.
def Cloth.move(
  +c: Cloth, +i: U32, +stride: U32, +fit: Fit, +o: Vec, +face: F32, +t: F32, +drop: F32
) -> Cloth:
  match c:
    case Thread{p, old}:
      Fit{cols, _, _, _, _, _, _, len, _, _, _, _, _} = fit
      +k = (len * 1.282 : F32)
      +target = Cloth.home(i, fit, o, drop, face)
      +free = Math.pick((i >= cols : U32), 1.0, 0.0)
      +motion = Cloth.limit(Vec.scale(Vec.sub(p, old), 0.94), (0.38 * k : F32))
      +wind = Vec.scale(Vec{(0.0018 * F32.sin((t * 0.031 + U32.to_f32(i) * 0.7 : F32)) : F32),
        (0.0 - 0.005 : F32), (0.001 * F32.sin((t * 0.043 : F32)) : F32)}, k)
      +next = Vec.add(Vec.add(p, motion), Vec.add(wind, Vec.scale(Vec.sub(target, p), 0.025)))
      Thread{Vec.mix(target, Vec.add(target, Cloth.limit(Vec.sub(next, target), (0.85 * k : F32))),
          free), Vec.mix(target, p, free)}
    case Weave{a, b, cc, d}:
      +s = (stride / 4 : U32)
      Weave{Cloth.move(a, i, s, fit, o, face, t, drop),
        Cloth.move(b, (i + stride : U32), s, fit, o, face, t, drop),
        Cloth.move(cc, (i + stride * 2 : U32), s, fit, o, face, t, drop),
        Cloth.move(d, (i + stride * 3 : U32), s, fit, o, face, t, drop)}

# The pull of particle j on p (particle i) toward their rest distance.
def Cloth.pull(+all: Cloth, +i: U32, +j: U32, +fit: Fit, +p: Vec) -> Vec:
  +delta = Vec.sub(Cloth.at(3n, all, j, 16), p)
  +dist = Vec.len(delta)
  +len = Vec.len(Vec.sub(Cloth.rest(i, fit, Vec{0.0, 0.0, 0.0}, 0.0),
    Cloth.rest(j, fit, Vec{0.0, 0.0, 0.0}, 0.0)))
  Vec.scale(delta, ((dist - len) / Math.max(0.00001, dist) : F32))

# A local point pushed out of the body (its radius between lo and hi)
# and off the floor.
def Cloth.hold(+local: Vec, +fit: Fit, +o: Vec) -> Vec:
  Vec{x, y, z} = local
  Fit{_, _, open, _, _, _, _, _, _, tie, body, lo, hi} = fit
  +rad = F32.sqrt((x * x + z * z : F32))
  +push = Math.pick(((y > lo) && (y < hi) : F32),
    Math.max(1.0, (body / Math.max(0.001, rad) : F32)), 1.0)
  Vec.add(o, Vec{(x * push : F32), Math.max(0.035, y), (z * push : F32)})

# A Jacobi pass: each thread moves 0.24 of the pull of its neighbours
# (the ring wraps unless open; the tie scales the pull across) in the
# snapshot all, then is held.
def Cloth.solve(
  +c: Cloth, +all: Cloth, +i: U32, +stride: U32, +fit: Fit, +o: Vec, +face: F32, +drop: F32
) -> Cloth:
  match c:
    case Thread{p, old}:
      Fit{cols, rows, open, _, _, _, _, _, _, tie, _, _, _} = fit
      +col = (i % cols : U32)
      +row = (i / cols : U32)
      +ring = U32.is_eq(open, 0)
      +l = Math.word((col > 0 : U32), (i - 1 : U32), Math.word(ring, (i + cols - 1 : U32), i))
      +r = Math.word(((col + 1 : U32) < cols : U32), (i + 1 : U32),
        Math.word(ring, (i + 1 - cols : U32), i))
      +force = Vec.add(Vec.scale(Vec.add(Cloth.pull(all, i, l, fit, p),
            Cloth.pull(all, i, r, fit, p)), tie),
        Vec.add(Cloth.pull(all, i, Math.word((row > 0 : U32), (i - cols : U32), i), fit, p),
          Cloth.pull(all, i, Math.word(((row + 1 : U32) < rows : U32), (i + cols : U32), i),
            fit, p)))
      +safe = Cloth.hold(Vec.sub(Vec.add(p, Vec.scale(force, 0.24)), o), fit, o)
      Thread{Vec.mix(Cloth.home(i, fit, o, drop, face), safe,
        Math.pick((i >= cols : U32), 1.0, 0.0)), old}
    case Weave{a, b, cc, d}:
      +s = (stride / 4 : U32)
      Weave{Cloth.solve(a, all, i, s, fit, o, face, drop),
        Cloth.solve(b, all, (i + stride : U32), s, fit, o, face, drop),
        Cloth.solve(cc, all, (i + stride * 2 : U32), s, fit, o, face, drop),
        Cloth.solve(d, all, (i + stride * 3 : U32), s, fit, o, face, drop)}

def Cloth.relax(n: Nat, +c: Cloth, +fit: Fit, +o: Vec, +face: F32, +drop: F32) -> Cloth:
  match n:
    case 0n:
      c
    case 1n+k:
      Cloth.relax(k, Cloth.solve(c, c, 0, 16, fit, o, face, drop), fit, o, face, drop)

# The cloth a tick later about its anchor o facing face at the time t,
# lowered by drop: the Verlet step, then three Jacobi passes.
def Cloth.step(+c: Cloth, +fit: Fit, +o: Vec, +face: F32, +t: F32, +drop: F32) -> Cloth:
  Cloth.relax(3n, Cloth.move(c, 0, 16, fit, o, face, t, drop), fit, o, face, drop)

def Cloth.lerp(+a: Cloth, +b: Cloth, +u: F32) -> Cloth:
  match a b:
    case Thread{p0, o0} Thread{p, o}:
      Thread{Vec.mix(p0, p, u), Vec.mix(o0, o, u)}
    case Weave{a0, b0, c0, d0} Weave{a1, b1, c1, d1}:
      Weave{Cloth.lerp(a0, a1, u), Cloth.lerp(b0, b1, u), Cloth.lerp(c0, c1, u),
        Cloth.lerp(d0, d1, u)}
    case _ _:
      b

def Sheet.of(
  +a: Vec, +b: Vec, +c: Vec, +d: Vec, +e: Vec, +f: Vec, +g: Vec, +h: Vec
) -> Surf:
  Vec{ax, ay, az} = a
  Vec{bx, by, bz} = b
  Vec{cx, cy, cz} = c
  Vec{dx, dy, dz} = d
  Vec{ex, ey, ez} = e
  Vec{fx, fy, fz} = f
  Vec{gx, gy, gz} = g
  Vec{hx, hy, hz} = h
  Sheet{ax, ay, az, bx, by, bz, cx, cy, cz, dx, dy, dz, ex, ey, ez, fx, fy, fz, gx,
    gy, gz, hx, hy, hz}

# The patch under particle i: Catmull-Rom over its row from the column
# before to two after (the ring wraps, an open cloth clamps), and the
# row below, 2 x 2 (an open cloth, a small mantle, 1 x 1); the columns
# alternate two tints.
def Cloth.patch(+c: Cloth, +i: U32, +fit: Fit, +c0: U32, +c1: U32, +cam: Cam) -> Cells:
  Fit{cols, _, open, _, _, _, _, _, flat, _, _, _, _} = fit
  +row = ((i / cols) * cols : U32)
  +col = (i % cols : U32)
  +ring = U32.is_eq(open, 0)
  +l = (row + Math.word(ring, ((col + cols - 1) % cols : U32),
    Math.word((col > 0 : U32), (col - 1 : U32), col)) : U32)
  +r = (row + Math.word(ring, ((col + 1) % cols : U32), (col + 1 : U32)) : U32)
  +rr = (row + Math.word(ring, ((col + 2) % cols : U32),
    Math.word(((col + 2 : U32) < cols : U32), (col + 2 : U32), (col + 1 : U32))) : U32)
  Mesh.of(Sheet.of(Cloth.at(3n, c, l, 16), Cloth.at(3n, c, i, 16), Cloth.at(3n, c, r, 16),
      Cloth.at(3n, c, rr, 16), Cloth.at(3n, c, (l + cols : U32), 16),
      Cloth.at(3n, c, (i + cols : U32), 16), Cloth.at(3n, c, (r + cols : U32), 16),
      Cloth.at(3n, c, (rr + cols : U32), 16)),
    Mat.paint(Math.word(U32.is_eq((i % 4 : U32), 0), c0, c1), 0.84, 0.0, 0.0),
    Math.word(ring, 2, 1), Math.word(ring, 2, 1), cam)

# The strand from particle i to the one below: a flat ribbon facing
# the eye, w wide each side of the line (wound to face the eye).
def Cloth.rope(+c: Cloth, +i: U32, +fit: Fit, +c0: U32, +w: F32, +cam: Cam) -> Cells:
  Fit{cols, _, _, _, _, _, _, _, _, _, _, _, _} = fit
  Cam{ex, ey, ez, _, _, _, _, _} = cam
  +a = Cloth.at(3n, c, i, 16)
  +b = Cloth.at(3n, c, (i + cols : U32), 16)
  +axis = Vec.sub(b, a)
  +right = Vec.unit(Vec.cross(axis, Vec.sub(Vec{ex, ey, ez}, a)))
  Mesh.of(Inst.of(Plate{}, Vec.mix(a, b, 0.5), Vec.scale(right, w), Vec{0.0, 0.0, 0.0},
    Vec.scale(axis, (0.0 - 0.5 : F32))), Mat.paint(c0, 0.7, 0.0, 0.0), 1, 1, cam)

def Cloth.piece(
  skip: Bool, rope: Bool, +c: Cloth, +i: U32, +fit: Fit, +c0: U32, +c1: U32, +w: F32, +cam: Cam
) -> Cells:
  match skip rope:
    case True{} _:
      CNil{}
    case False{} False{}:
      Cloth.patch(c, i, fit, c0, c1, cam)
    case False{} True{}:
      Cloth.rope(c, i, fit, c0, w, cam)

# The pieces of a cloth (patches, or ropes of a width), a fork tree
# over 64: none under the last row, nor past an open cloth's last
# column.
def Cloth.mesh(
  +n: Nat, +c: Cloth, +i: U32, +fit: Fit, +rope: Bool, +c0: U32, +c1: U32, +w: F32, +cam: Cam
) -> Cells:
  match n:
    case 0n:
      Fit{cols, rows, open, _, _, _, _, _, _, _, _, _, _} = fit
      Cloth.piece((((i / cols) + 1 : U32) >= rows : U32) || (Bool.not(rope) && U32.is_eq(open, 1)
          && U32.is_eq((i % cols : U32), (cols - 1 : U32))), rope, c, i, fit, c0, c1, w, cam)
    case 1n+k:
      +s = U32.shln(1, (k + k : Nat))
      a b cc d = Cloth.mesh(k, c, i, fit, rope, c0, c1, w, cam)
        Cloth.mesh(k, c, (i + s : U32), fit, rope, c0, c1, w, cam)
        Cloth.mesh(k, c, (i + s * 2 : U32), fit, rope, c0, c1, w, cam)
        Cloth.mesh(k, c, (i + s * 3 : U32), fit, rope, c0, c1, w, cam)
      Cells.m4(a, b, cc, d)

# The hero's cape: 56 patches in two reds.
def Cape.of(+c: Cloth, +cam: Cam) -> Cells:
  Cloth.mesh(3n, c, 0, Fit.cape(), False{}, 12199235, 10423856, 0.0, cam)

# The boss's cloths: a long cloak from the shoulders, a mantle over the
# back of the hood, six strands of hair from under it (loose ropes);
# each about the anchor at its feet under the torso.
type Garb is Data:
  Garb{cloak: Cloth, hood: Cloth, hair: Cloth}

def Fit.cloak() -> Fit:
  Fit{8, 8, 0, 0.42, 0.75, 1.1, 3.15, 2.85, 0.6, 1.0, 0.45, 1.4, 3.3}

def Fit.hood() -> Fit:
  Fit{8, 8, 1, 0.62, 0.30, 0.15, 3.78, 1.2, 1.0, 1.0, 0.55, 2.4, 3.8}

def Fit.hair() -> Fit:
  Fit{6, 10, 1, 0.34, 0.0, 0.9, 3.55, 2.4, 1.0, 0.0, 0.5, 2.2, 3.7}

def Garb.seed(+o: Vec, +face: F32) -> Garb:
  Garb{Cloth.seed(3n, 0, Fit.cloak(), o, face), Cloth.seed(3n, 0, Fit.hood(), o, face),
    Cloth.seed(3n, 0, Fit.hair(), o, face)}

def Garb.step(+g: Garb, +o: Vec, +face: F32, +t: F32) -> Garb:
  Garb{cloak, hood, hair} = g
  a b c = Cloth.step(cloak, Fit.cloak(), o, face, t, 0.0) Cloth.step(hood, Fit.hood(), o, face, t, 0.0)
    Cloth.step(hair, Fit.hair(), o, face, t, 0.0)
  Garb{a, b, c}

def Garb.lerp(+a: Garb, +b: Garb, +u: F32) -> Garb:
  Garb{c0, h0, r0} = a
  Garb{cloak, hood, hair} = b
  Garb{Cloth.lerp(c0, cloak, u), Cloth.lerp(h0, hood, u), Cloth.lerp(r0, hair, u)}

def Garb.build(+g: Garb, +cam: Cam) -> Cells:
  Garb{cloak, hood, hair} = g
  a b c = Cloth.mesh(3n, cloak, 0, Fit.cloak(), False{}, 1186352, 725024, 0.0, cam)
    Cloth.mesh(3n, hood, 0, Fit.hood(), False{}, 725024, 1186352, 0.0, cam)
    Cloth.mesh(3n, hair, 0, Fit.hair(), True{}, 3162206, 0, 0.045, cam)
  Cells.merge(a, Cells.merge(b, c))

# Sim
# ---

# The hero: place, speed, facing (0 is +x, pi is -x), damage, guard,
# the jump bits (two count jumps, 8 the air dodge spent, 16 the
# recovery), the action and its age (down for attacks, dodges and hurt,
# up for a guard), the invulnerable ticks, the lives, the coyote grace,
# the jump buffer and the smash charge. Actions: 0 idle, 1 neutral, 2
# neutral special, 3 guard, 4 hurt, 5 landing, 6 air dodge, 7 crouch,
# 10-12 side/up/down, 13-17 air neutral/forward/back/up/down, 20-22
# side/up/down special, 23-26 their air kinds, 30-32 smashes charging.
type Fighter is Data:
  Fighter{p: Vec, v: Vec, face: F32, damage: F32, guard: F32, jumps: U32, action: U32,
    age: U32, inv: U32, stocks: U32, grace: U32, queued: U32, charge: U32}

# The boss, THE SEVERANT (Boss.name): a hooded swordsman 2.4 times
# the hero. Its place, its speed (the knockback and the leap), its
# facing, vitality, stun ticks, strain, its state (0 stalks, 1
# cleaves, 2 sweeps, 3 lunges, 4 leaps, 5 draws, 6 blocks and
# counters, 7 lands the slam), the state's age, the stalk's pause,
# the leap's mark (the hero's x) and the last walk (for the gait).
type Boss is Data:
  Boss{p: Vec, v: Vec, face: F32, hp: F32, stun: U32, strain: F32, state: U32, age: U32,
    hold: U32, mark: F32, gait: F32}

# A death's detonation: where, the tick it began and who died (1 the
# hero, 2 the boss).
type Blast is Data:
  Blast{x: F32, y: F32, born: U32, who: U32}

# Is the detonation over (42 ticks), or none?
def Blast.over(+m: Maybe<&2, Blast>, +time: U32) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{b}:
      Blast{_, _, born, _} = b
      ((time - born : U32) >= 42 : U32)

# The game: the tick, the keys held (W 1, A 2, S 4, D 8, J 16, K 32, I
# 64, L 128, R 512, P 1024) and tapped since the last tick, the mode (0
# title, 1 fight, 2 win, 3 loss, 4 pause), the hero, the boss, the
# hitstop flash, the cape's cloth, the boss's cloths, the lens, the
# last death's detonation.
type Game is Data:
  Game{time: U32, held: U32, taps: U32, mode: U32, hero: Fighter, boss: Boss, flash: U32,
    cloth: Cloth, garb: Garb, lens: Lens, blast: Maybe<&2, Blast>}

def Sim.dec(+x: U32) -> U32:
  Math.word((x > 0 : U32), (x - 1 : U32), 0)

def Sim.has(+held: U32, +bit: U32) -> Bool:
  U32.is_ne((held .&. bit : U32), 0)

def Sim.axis(+held: U32, +pos: U32, +neg: U32) -> F32:
  (Math.pick(Sim.has(held, pos), 1.0, 0.0) - Math.pick(Sim.has(held, neg), 1.0, 0.0) : F32)

def Vec.x(+p: Vec) -> F32:
  Vec{x, _, _} = p
  x

def Vec.y(+p: Vec) -> F32:
  Vec{x, y, z} = p
  y

# Combat lies in the x/y plane; a direction lies in x/z (facing).
def Vec.plane(+p: Vec) -> Vec:
  Vec{x, y, _} = p
  Vec{x, y, 0.0}

def Vec.dir(+a: Vec, +b: Vec) -> Vec:
  Vec{ax, _, az} = a
  Vec{bx, _, bz} = b
  Vec.unit(Vec{(bx - ax : F32), 0.0, (bz - az : F32)})

def Vec.facing(+v: Vec) -> F32:
  Vec{x, _, z} = v
  F32.atan2((0.0 - z : F32), x)

def Vec.dist(+a: Vec, +b: Vec) -> F32:
  Vec.len(Vec.sub(a, b))

# The distance from p to the segment a..b.
def Vec.seg(+p: Vec, +a: Vec, +b: Vec) -> F32:
  +ab = Vec.sub(b, a)
  +u = Math.sat((Vec.dot(Vec.sub(p, a), ab) / Math.max(0.0001, Vec.dot(ab, ab)) : F32))
  Vec.dist(p, Vec.add(a, Vec.scale(ab, u)))

# Past the blast zones.
def Vec.out(+p: Vec) -> Bool:
  Vec{x, y, _} = p
  ((y < (0.0 - 8.5)) || (y > 14.0) || (F32.abs(x) > 14.5) : F32)

def Act.in(+act: U32, +a: U32, +b: U32) -> Bool:
  ((act >= a) && (act <= b) : U32)

def Act.is(+act: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> Bool:
  (U32.is_eq(act, a) || U32.is_eq(act, b) || U32.is_eq(act, c) || U32.is_eq(act, d))

# The upward attacks, the downward ones, the specials, every attack,
# the smashes charging, the crouching actions (1), an attack's length
# in ticks, the age its hit lands at, and a charge's power.
def Act.up(+act: U32) -> Bool:
  Act.is(act, 11, 16, 21, 25)

def Act.down(+act: U32) -> Bool:
  Act.is(act, 12, 17, 22, 26)

def Act.special(+act: U32) -> Bool:
  Bool.or(U32.is_eq(act, 2), Act.in(act, 20, 29))

def Act.attack(+act: U32) -> Bool:
  Bool.or(U32.is_eq(act, 1), Bool.or(U32.is_eq(act, 2), Act.in(act, 10, 29)))

def Act.charging(+act: U32) -> Bool:
  Act.in(act, 30, 32)

def Act.crouch(+act: U32) -> F32:
  Math.pick(Act.is(act, 7, 12, 32, 32), 1.0, 0.0)

def Act.length(+act: U32) -> U32:
  Math.word(Act.special(act), Math.word(Act.down(act), 42, 34),
    Math.word(Bool.or(U32.is_eq(act, 12), U32.is_eq(act, 17)), 25,
      Math.word(U32.is_eq(act, 1), 18, 21)))

def Act.hit(+act: U32) -> U32:
  (Act.length(act) - Math.word(Act.special(act), 9, 5) : U32)

def Act.power(+charge: U32) -> F32:
  (1.0 + Math.sat((U32.to_f32(charge) / 45.0 : F32)) * 1.3 : F32)

def Fighter.spawn(+p: Vec, +stocks: U32, +inv: U32) -> Fighter:
  Fighter{Vec.plane(p), Vec{0.0, 0.0, 0.0}, 0.0, 0.0, 100.0, 0, 0, 0, inv, stocks, 6, 0, 0}

# A fresh game: the hero at -3.4, the boss at 3.2 facing him, 360
# vitality.
def Game.fresh(+held: U32, +mode: U32) -> Game:
  +home = {Vec{(0.0 - 3.4 : F32), 0.0, 0.0} : Vec}
  Game{0, held, 0, mode, Fighter.spawn(home, 3, 0),
    Boss{Vec{3.2, 0.0, 0.0}, Vec{0.0, 0.0, 0.0}, 3.14159, 360.0, 0, 0.0, 0, 0, 40, 0.0, 0.0}, 0,
    Cloth.seed(3n, 0, Fit.cape(), home, 0.0), Garb.seed(Vec{3.2, 0.0, 0.0}, 3.14159),
    Lens{0.0, 2.6, 25.0, 0.0, 0.0, 0.0}, None{}}

def Game.init() -> Game:
  Game.fresh(0, 0)

def Key.bit(+c: U32, +code: U32, +bit: U32) -> U32:
  Math.word(U32.is_eq(c, code), bit, 0)

# The bit of a key: w a s d j k i l r p, the arrows as w s a d.
def Key.mask(+c: U32) -> U32:
  (Key.bit(c, 119, 1) .|. Key.bit(c, 97, 2) .|. Key.bit(c, 115, 4) .|. Key.bit(c, 100, 8)
    .|. Key.bit(c, 106, 16) .|. Key.bit(c, 107, 32) .|. Key.bit(c, 105, 64)
    .|. Key.bit(c, 108, 128) .|. Key.bit(c, 63232, 1) .|. Key.bit(c, 63233, 4)
    .|. Key.bit(c, 63234, 2) .|. Key.bit(c, 63235, 8) .|. Key.bit(c, 114, 512)
    .|. Key.bit(c, 112, 1024) : U32)

# A key event: its bit in held; a press of a key not held is a tap.
def Game.key(+g: Game, +code: U32, +down: Bool) -> Game:
  Game{time, held, taps, mode, hero, boss, flash, cloth, garb, lens, blast} = g
  +m = Key.mask(Math.word(((code >= 65) && (code <= 90) : U32), (code + 32 : U32), code))
  Game{time, Math.word(down, (held .|. m : U32), (held .&. U32.not(m) : U32)),
    (taps .|. Math.word((down && Bool.not(Sim.has(held, m))), m, 0) : U32), mode, hero, boss,
    flash, cloth, garb, lens, blast}

def Game.keys(+g: Game, +h: U32, +t: U32) -> Game:
  Game{time, held, taps, mode, hero, boss, flash, cloth, garb, lens, blast} = g
  Game{time, h, (taps .|. t : U32), mode, hero, boss, flash, cloth, garb, lens, blast}

# The ground a fall from old to p lands on: the base (|x| <= 7.3) at 0,
# the sides (||x| - 4.5| < 1.5) at 2.15, the top (|x| < 1.55) at 3.65,
# none (-100); S held drops through the platforms.
def Stage.landing(+p: Vec, +old: F32, +through: Bool) -> F32:
  Vec{x, y, _} = p
  +base = ((F32.abs(x) <= 7.3) && (old >= 0.0) && (y <= 0.0) : F32)
  +side = (Bool.not(through) && ((F32.abs((F32.abs(x) - 4.5 : F32)) < 1.5)
    && (old >= 2.15) && (y <= 2.15) : F32))
  +top = (Bool.not(through) && ((F32.abs(x) < 1.55) && (old >= 3.65) && (y <= 3.65) : F32))
  Math.pick(top, 3.65, Math.pick(side, 2.15, Math.pick(base, 0.0, (0.0 - 100.0 : F32))))

def Vec.place(+p: Vec, +level: F32, +landed: Bool) -> Vec:
  Vec{x, y, _} = p
  Vec{x, Math.pick(landed, level, y), 0.0}

def Fighter.air(+p: Vec, +v: Vec) -> Bool:
  ((F32.abs(Vec.y(v)) > 0.005 : F32) || (Vec.y(p) > (Stage.landing(Vec.add(p,
    Vec{0.0, (0.0 - 0.025 : F32), 0.0}), Vec.y(p), False{}) + 0.04 : F32) : F32))

# The attack the keys pick: K a special, J a normal; up, down, a side
# (back in the air when held against the facing) or neutral.
def Fighter.kind(+special: Bool, +air: Bool, +held: U32, +face: F32) -> U32:
  +up = Sim.has(held, 1)
  +down = Sim.has(held, 4)
  +side = (Sim.has(held, 2) || Sim.has(held, 8))
  +back = ((Sim.axis(held, 8, 2) * F32.cos(face) : F32) < (0.0 - 0.1 : F32) : F32)
  Math.word(special,
    Math.word(air, Math.word(up, 25, Math.word(down, 26, Math.word(side, 24, 23))),
      Math.word(up, 21, Math.word(down, 22, Math.word(side, 20, 2)))),
    Math.word(air, Math.word(up, 16, Math.word(down, 17, Math.word(side,
        Math.word(back, 15, 14), 13))),
      Math.word(up, 11, Math.word(down, 12, Math.word(side, 10, 1)))))

# The hero a tick later under the keys: his action (a block, a dodge,
# an attack, a smash wound up, charged and released, a crouch) and its
# timer, his facing, his speed, the ground, the landing lag, the guard,
# the jump bits, the grace, the buffer, the charge.
def Fighter.tick(+f: Fighter, +held: U32, +taps: U32) -> Fighter:
  Fighter{p, v, face, damage, guard, jumps, action, age, inv, stocks, grace, queued, charge} = f
  Vec{_, y, _} = p
  Vec{vx, vy, _} = v
  +air = Fighter.air(p, v)
  +broken = (U32.is_eq(action, 3) && (guard <= 1.0 : F32))
  +hurt = (U32.is_eq(action, 4) && (age > 0 : U32))
  +block = (Bool.not(air) && (Sim.has(held, 128) || Sim.has(taps, 128)) && (guard > 1.0 : F32)
    && Bool.not(hurt))
  +count = (jumps .&. 3 : U32)
  +used = Math.word((air && U32.is_eq(grace, 0) && U32.is_eq(count, 0)), 1, count)
  +jump = ((Sim.has(taps, 64) || (queued > 0 : U32)) && (used < 2 : U32) && Bool.not(block)
    && Bool.not(hurt) && Bool.not(U32.is_eq(action, 6)) && Bool.not(U32.is_eq(action, 5))
    && Bool.not(Act.charging(action)))
  +free = ((age <= 1 : U32) || U32.is_eq(action, 3) || U32.is_eq(action, 7))
  +special = (Sim.has(taps, 32) && free && Bool.not(block) && Bool.not(hurt)
    && Bool.not((air && Sim.has(held, 1) && Sim.has(jumps, 16))))
  +attack = ((Sim.has(held, 16) || Sim.has(taps, 16)) && free && Bool.not(block)
    && Bool.not(special) && Bool.not(hurt))
  +chosen = Fighter.kind(special, air, held, face)
  +dodge = (air && Sim.has(taps, 128) && free && Bool.not(hurt) && Bool.not(Sim.has(jumps, 8)))
  +crouch = (Bool.not(air) && Sim.has(held, 4) && free && Bool.not(block))
  +winding = (Act.in(action, 10, 12) && Sim.has(held, 16)
    && U32.is_eq(age, (Act.length(action) - 2 : U32)))
  +loading = (Act.charging(action) && Sim.has(held, 16) && (charge < 60 : U32) && Bool.not(block))
  +release = (Act.charging(action) && Bool.not(loading) && Bool.not(block))
  +act = Math.word(dodge, 6, Math.word(winding, (action + 20 : U32), Math.word(loading, action,
    Math.word(release, (action - 20 : U32), Math.word(block, 3, Math.word((special || attack),
    chosen, Math.word(((age > 1 : U32) && Bool.not(U32.is_eq(action, 3))), action,
    Math.word(crouch, 7, 0))))))))
  +timer = Math.word(dodge, 28, Math.word((winding || loading), 61,
    Math.word(release, (Act.hit((action - 20 : U32)) + 2 : U32),
      Math.word(block, Math.word(U32.is_eq(action, 3), (age + 1 : U32), 1),
        Math.word((special || attack), Act.length(chosen),
          Math.word(U32.is_eq(action, 3), 0, Sim.dec(age)))))))
  +dx = Sim.axis(held, 8, 2)
  +aim = Math.pick(((F32.abs(dx) > 0.1 : F32) && Bool.not(air) && Bool.not(hurt)),
    Vec.facing(Vec{dx, 0.0, 0.0}), face)
  +side = (U32.is_eq(act, 20) || U32.is_eq(act, 24))
  +rise = (special && Act.up(act))
  +dive = (special && Act.down(act) && air)
  +burst = (side && (timer > 20 : U32))
  +speed = Math.pick((loading || winding), 0.0, Math.pick(crouch, 0.016, Math.pick(block, 0.009,
    Math.pick(hurt, 0.008, Math.pick(air, 0.025, 0.061)))))
  +normal = Math.clamp((vx * Math.pick(hurt, 0.965, Math.pick(air, 0.91, 0.77)) + dx * speed : F32),
    Math.pick(hurt, (0.0 - 2.0 : F32), (0.0 - 0.31 : F32)), Math.pick(hurt, 2.0, 0.31))
  +evading = (U32.is_eq(action, 6) && (age > 14 : U32))
  +escape = Vec.scale(Vec.unit(Vec{dx, Sim.axis(held, 1, 4), 0.0}), 0.40)
  +nx = Math.pick(dodge, Vec.dot(escape, Vec{1.0, 0.0, 0.0}), Math.pick(evading, (vx * 0.93 : F32),
    Math.pick(burst, (Math.pick((F32.abs(dx) > 0.1 : F32), dx, F32.cos(aim)) * 0.40 : F32),
      Math.pick(rise, (dx * 0.12 : F32), normal))))
  +gravity = Math.pick((Sim.has(held, 4) && (vy < 0.0 : F32)), 0.040, 0.020)
  +fall = Math.max((0.0 - 0.65 : F32), (vy - gravity : F32))
  +hop = Math.pick((Bool.not(Sim.has(held, 64)) && (vy > 0.19 : F32)
    && Bool.not(Act.special(action)) && Bool.not(hurt)), Math.min(fall, 0.19), fall)
  +ny = Math.pick(dodge, Vec.y(escape), Math.pick(evading, (vy * 0.93 : F32),
    Math.pick(jump, 0.39, Math.pick(rise, 0.48, Math.pick(dive, (0.0 - 0.52 : F32), hop)))))
  +next = Vec.add(Vec.plane(p), Vec{nx, ny, 0.0})
  +floor = Stage.landing(next, y, Sim.has(held, 4))
  +ground = (floor > (0.0 - 99.0 : F32) : F32)
  +landlag = (air && ground && (Act.attack(action) || U32.is_eq(action, 6)) && (age > 1 : U32))
  Fighter{Vec.place(next, floor, ground), Vec{nx, Math.pick(ground, 0.0, ny), 0.0}, aim, damage,
    Math.clamp((guard + Math.pick(block, (0.0 - 0.65 : F32), 0.55) : F32), 0.0, 100.0),
    Math.word(ground, 0, (Math.word(jump, Math.word((grace > 0 : U32), 1, (used + 1 : U32)), used)
      .|. (jumps .&. 24) .|. Math.word(dodge, 8, 0) .|. Math.word(rise, 16, 0) : U32)),
    Math.word(broken, 4, Math.word(landlag, 5, act)),
    Math.word(broken, 45, Math.word(landlag, 8, timer)), Math.word(dodge, 12, Sim.dec(inv)),
    stocks, Math.word(jump, 0, Math.word(ground, 6, Sim.dec(grace))),
    Math.word(jump, 0, Math.word(Sim.has(taps, 64), 6, Sim.dec(queued))),
    Math.word((loading || winding), (charge + 1 : U32),
      Math.word((attack || special || U32.is_eq(act, 0)), 0, charge))}

def Boss.name() -> String:
  "THE SEVERANT"

def Boss.tab(
  +s: U32, +a: U32, +b: U32, +c: U32, +d: U32, +e: U32, +f: U32, +g: U32, +h: U32
) -> U32:
  Math.word(U32.is_eq(s, 0), a, Math.word(U32.is_eq(s, 1), b, Math.word(U32.is_eq(s, 2), c,
    Math.word(U32.is_eq(s, 3), d, Math.word(U32.is_eq(s, 4), e, Math.word(U32.is_eq(s, 5), f,
      Math.word(U32.is_eq(s, 6), g, h)))))))

# A state's wind-up, active and recovery ticks (the leap's recovery
# lasts to the landing; the landing strikes at once), their sum, and
# is its blade live at an age?
def Boss.wind(+s: U32) -> U32:
  Boss.tab(s, 100000, 30, 18, 16, 12, 46, 6, 0)

def Boss.act(+s: U32) -> U32:
  Boss.tab(s, 0, 8, 8, 10, 10, 4, 6, 6)

def Boss.rec(+s: U32) -> U32:
  Boss.tab(s, 0, 26, 22, 24, 1000, 36, 14, 30)

def Boss.len(+s: U32) -> U32:
  (Boss.wind(s) + Boss.act(s) + Boss.rec(s) : U32)

def Boss.live(+s: U32, +age: U32) -> Bool:
  ((age >= Boss.wind(s)) && (age < (Boss.wind(s) + Boss.act(s) : U32)) : U32)

# An attack's damage to the hero and the scale of its knockback.
def Boss.blow(+s: U32) -> F32:
  U32.to_f32(Boss.tab(s, 0, 17, 12, 14, 20, 24, 12, 20))

def Boss.push(+s: U32) -> F32:
  (U32.to_f32(Boss.tab(s, 10, 10, 8, 10, 13, 15, 8, 13)) * 0.1 : F32)

# A pose: the grip (local: x ahead, y up, z aside), the blade's pitch
# and yaw (0 ahead, pi behind), the hips' dip and the torso's lean.
type Pose is Data:
  Pose{gx: F32, gy: F32, gz: F32, th: F32, yw: F32, dip: F32, lean: F32}

# A generic pick loses the callee's borrow facts (two shares in
# Boss.pose), so the poses keep their own.
def Pose.pick(c: Bool, +a: Pose, +b: Pose) -> Pose:
  match c:
    case True{}:
      a
    case False{}:
      b

def Pose.mix(+a: Pose, +b: Pose, +t: F32) -> Pose:
  Pose{ax, ay, az, ath, ayw, adip, alean} = a
  Pose{bx, by, bz, bth, byw, bdip, blean} = b
  Pose{Math.mix(ax, bx, t), Math.mix(ay, by, t), Math.mix(az, bz, t), Math.mix(ath, bth, t),
    Math.mix(ayw, byw, t), Math.mix(adip, bdip, t), Math.mix(alean, blean, t)}

# The keys: at rest (the blade over the shoulder), in flight, reeling
# (stunned), and of a state at the end of its wind-up and of its
# strike (the leap's is its flight; the landing's wind-up key is the
# flight's; the counter cuts low from the block).
def Pose.rest() -> Pose:
  Pose{0.35, 2.95, 0.35, 1.85, 0.2, 0.0, 0.0}

def Pose.flight() -> Pose:
  Pose{0.1, 4.0, 0.25, 2.3, 0.1, 0.0, (0.0 - 0.1 : F32)}

def Pose.reel() -> Pose:
  Pose{0.1, 1.7, 0.4, (0.0 - 1.1 : F32), 0.6, 0.25, (0.0 - 0.45 : F32)}

def Pose.wind(+s: U32) -> Pose:
  Pose.pick(U32.is_eq(s, 1), Pose{(0.0 - 0.35 : F32), 3.9, 0.3, 2.75, 0.1, 0.1, (0.0 - 0.25 : F32)},
    Pose.pick(U32.is_eq(s, 2), Pose{(0.0 - 0.4 : F32), 1.25, 0.55, 0.05, 2.5, 0.55, 0.1},
      Pose.pick(U32.is_eq(s, 3), Pose{(0.0 - 0.6 : F32), 2.35, 0.35, 0.0, 0.35, 0.25, (0.0 - 0.3 : F32)},
        Pose.pick(U32.is_eq(s, 4), Pose{0.2, 2.6, 0.3, 1.6, 0.2, 0.7, 0.2},
          Pose.pick(U32.is_eq(s, 5), Pose{(0.0 - 0.3 : F32), 1.5, 0.45, 0.0, 2.95, 0.3, 0.05},
            Pose.pick(U32.is_eq(s, 6), Pose{0.7, 2.3, 0.0, 1.5, 0.0, 0.15, 0.0},
              Pose.pick(U32.is_eq(s, 7), Pose.flight(), Pose.rest())))))))

def Pose.strike(+s: U32) -> Pose:
  Pose.pick(U32.is_eq(s, 1), Pose{1.1, 1.6, 0.15, (0.0 - 0.45 : F32), 0.0, 0.3, 0.5},
    Pose.pick(U32.is_eq(s, 2), Pose{0.9, 1.05, (0.0 - 0.3 : F32), 0.05, (0.0 - 0.7 : F32), 0.55, 0.35},
      Pose.pick(U32.is_eq(s, 3), Pose{1.3, 2.1, 0.1, (0.0 - 0.42 : F32), 0.0, 0.3, 0.7},
        Pose.pick(U32.is_eq(s, 4), Pose.flight(),
          Pose.pick(U32.is_eq(s, 5),
            Pose{0.8, 1.3, (0.0 - 0.2 : F32), (0.0 - 0.12 : F32), (0.0 - 1.1 : F32), 0.5, 0.5},
            Pose.pick(U32.is_eq(s, 6),
              Pose{1.1, 1.0, (0.0 - 0.2 : F32), (0.0 - 0.15 : F32), (0.0 - 0.3 : F32), 0.5, 0.45},
              Pose.pick(U32.is_eq(s, 7), Pose{1.0, 1.2, 0.2, (0.0 - 0.6 : F32), 0.0, 0.55, 0.5},
                Pose.rest())))))))

# The pose of a state at an age: from rest to the wind-up key, to the
# strike key, back to rest, each eased; reeling when stunned.
def Boss.pose(+s: U32, +age: U32, +stun: U32) -> Pose:
  +a = U32.to_f32(age)
  +w = U32.to_f32(Boss.wind(s))
  +n = U32.to_f32(Boss.act(s))
  +kw = Pose.wind(s)
  +ks = Pose.strike(s)
  +pose = Pose.pick((a < w : F32), Pose.mix(Pose.rest(), kw, Math.smooth((a / w : F32))),
    Pose.pick((a < (w + n : F32) : F32), Pose.mix(kw, ks, Math.smooth(((a - w) / n : F32))),
      Pose.mix(ks, Pose.rest(), Math.smooth(((a - w - n) / U32.to_f32(Boss.rec(s)) : F32)))))
  Pose.mix(pose, Pose.reel(), Math.sat((U32.to_f32(stun) * 0.2 : F32)))

# A pose's grip, blade direction, spine (u from the hips, 0, to the
# head, 1) and the cloths' anchor, all local.
def Pose.grip(+k: Pose) -> Vec:
  Pose{gx, gy, gz, _, _, _, _} = k
  Vec{gx, gy, gz}

def Pose.dir(+k: Pose) -> Vec:
  Pose{_, _, _, th, yw, _, _} = k
  Vec{(F32.cos(th) * F32.cos(yw) : F32), F32.sin(th), (0.0 - F32.cos(th) * F32.sin(yw) : F32)}

def Pose.spine(+k: Pose, +u: F32) -> Vec:
  Pose{_, _, _, _, _, dip, lean} = k
  Vec{(lean * (0.25 + 0.75 * u) + 0.1 * u : F32), (1.75 + 1.75 * u - dip * (1.0 + 0.15 * u) : F32), 0.0}

def Pose.root(+k: Pose) -> Vec:
  Pose{_, _, _, _, _, dip, lean} = k
  Vec{(lean * 0.75 : F32), (0.0 - dip : F32), 0.0}

# A local point of the boss in the world; the blade's hilt and tip
# (3.1 along its direction); the cloths' anchor.
def Boss.at(+p: Vec, +face: F32, +local: Vec) -> Vec:
  Vec.add(p, Vec.turn(local, face))

def Boss.hilt(+p: Vec, +face: F32, +k: Pose) -> Vec:
  Boss.at(p, face, Pose.grip(k))

def Boss.tip(+p: Vec, +face: F32, +k: Pose) -> Vec:
  Boss.at(p, face, Vec.add(Pose.grip(k), Vec.scale(Pose.dir(k), 3.1)))

def Boss.anchor(+b: Boss) -> Vec:
  Boss{p, _, face, _, stun, _, state, age, _, _, _} = b
  Boss.at(p, face, Pose.root(Boss.pose(state, age, stun)))

# A pseudo-random byte of a tick.
def Boss.hash(+t: U32) -> U32:
  ((((t + 7) * 2654435761 : U32) >> 13n : U32) .&. 255 : U32)

# The next attack from the range and the hero: a leap at a hero in the
# air, a cleave, sweep or draw up close (a leap or a sweep at a guard),
# a lunge, leap or draw at mid range, none far off.
def Boss.choose(+gap: F32, +rise: F32, +act: U32, +seed: U32) -> U32:
  +r = (seed .&. 7 : U32)
  +near = (gap < 3.6 : F32)
  +mid = (gap < 7.0 : F32)
  Math.word(((rise > 1.2 : F32) && mid), 4,
    Math.word(near, Math.word(U32.is_eq(act, 3), Math.word((r < 4 : U32), 4, 2),
        Math.word((r < 5 : U32), 1, Math.word((r < 7 : U32), 2, 5))),
      Math.word(mid, Math.word((r < 3 : U32), 3, Math.word((r < 5 : U32), 4, 5)), 0)))

# The boss a tick later. Its mind: stunned, it reels in the stalk; a
# leap lands into the slam; a finished attack chains (enraged under
# 160: cleave to sweep, sweep to lunge) or stalks with a pause; a
# stalk past its pause, grounded and in range picks an attack. Its
# motion: the stalk walks to a spacing of 3.2 facing the hero within x
# +-6; the lunge dashes 0.6 a tick; the leap springs to its mark; the
# knockback decays 0.92; gravity; the ground; the blast zones. The
# age runs twice as fast enraged; dead, it holds as if stunned.
def Boss.tick(+b: Boss, +f: Fighter, +t: U32) -> Boss:
  Boss{p, v, face, hp, stun, strain, state, age, hold, mark, _} = b
  Vec{x, y, _} = p
  Vec{vx, vy, _} = v
  Fighter{q, _, _, _, _, _, action, _, _, _, _, _, _} = f
  Vec{hx, hy, _} = q
  +raging = (hp < 160.0 : F32)
  +step = Math.word(raging, 2, 1)
  +stunned = ((stun > 0 : U32) || (hp <= 0.0 : F32))
  +air = Fighter.air(p, v)
  +dx = (hx - x : F32)
  +dist = F32.abs(dx)
  +seed = Boss.hash(t)
  +done = ((state > 0 : U32) && ((age + step : U32) >= Boss.len(state) : U32))
  +landed = (U32.is_eq(state, 4) && (age > 14 : U32) && Bool.not(air))
  +ready = (U32.is_eq(state, 0) && (age >= hold : U32) && Bool.not(stunned) && Bool.not(air))
  +chain = Math.word((raging && U32.is_eq(state, 1)), 2, Math.word((raging && U32.is_eq(state, 2)), 3, 0))
  +s2 = Math.word(stunned, 0, Math.word(landed, 7, Math.word(done, chain,
    Math.word(ready, Boss.choose(dist, (hy - y : F32), action, seed), state))))
  +fresh = Bool.not(U32.is_eq(s2, state))
  +age2 = Math.word(fresh, 0, (age + Math.word(U32.is_eq(state, 0), 1, step) : U32))
  +hold2 = Math.word((fresh && U32.is_eq(s2, 0)), (14 + (seed .&. 15) : U32), hold)
  +mark2 = Math.pick((fresh && U32.is_eq(s2, 4)), Math.clamp(hx, (0.0 - 6.5 : F32), 6.5), mark)
  +toward = Math.pick((dx < 0.0 : F32), (0.0 - 1.0 : F32), 1.0)
  +walking = (U32.is_eq(s2, 0) && (age2 >= hold2 : U32) && Bool.not(stunned) && Bool.not(air))
  +walk = Math.pick(walking, (toward * Math.pick((dist > 3.5 : F32), 0.05,
    Math.pick((dist < 2.7 : F32), (0.0 - 0.03 : F32), 0.0)) : F32), 0.0)
  +lunging = (U32.is_eq(s2, 3) && Boss.live(3, age2))
  +dash = Math.pick(lunging, (F32.cos(face) * 0.6 : F32), 0.0)
  +leap = (U32.is_eq(s2, 4) && (age < 12 : U32) && (age2 >= 12 : U32))
  +vx2 = Math.pick(leap, ((mark2 - x) / 11.8 : F32), vx)
  +vy2 = Math.pick(leap, 0.34, vy)
  +lim = Math.pick((lunging || U32.is_eq(s2, 4)), 7.0, 6.0)
  +next = {Vec{(Math.clamp((x + walk + dash : F32), (0.0 - lim : F32), lim) + vx2 : F32),
    (y + vy2 : F32), 0.0} : Vec}
  +floor = Stage.landing(next, y, False{})
  +ground = (floor > (0.0 - 99.0 : F32) : F32)
  +pos = Vec.place(next, floor, ground)
  Boss{pos, Vec{(vx2 * 0.92 : F32), Math.pick(ground, 0.0, Math.max((0.0 - 0.65 : F32),
      (vy2 - 0.02 : F32))), 0.0},
    Math.pick((U32.is_eq(s2, 0) && Bool.not(stunned)), Vec.facing(Vec{dx, 0.0, 0.0}), face),
    Math.pick(Vec.out(pos), 0.0, hp), Sim.dec(stun), strain, s2, age2, hold2, mark2,
    (walk + dash : F32)}

# Does the boss's blade (live, its segment's shadow on the combat
# plane within 0.7 of the hero's chest) or its slam (the hero grounded
# within 2.5 in its first 6 ticks) strike him? Not while he is
# invulnerable, nor while it is stunned or dead.
def Boss.contact(+f: Fighter, +b: Boss) -> Bool:
  Fighter{q, _, _, _, _, _, _, _, inv, _, _, _, _} = f
  Boss{p, _, face, hp, stun, _, state, age, _, _, _} = b
  +k = Boss.pose(state, age, stun)
  +blade = (Boss.live(state, age) && (Vec.seg(Vec.add(q, Vec{0.0, 0.75, 0.0}),
    Vec.plane(Boss.hilt(p, face, k)), Vec.plane(Boss.tip(p, face, k))) < 0.7 : F32))
  +ring = (U32.is_eq(state, 7) && (age < 6 : U32) && (F32.abs((Vec.x(q) - Vec.x(p) : F32)) < 2.5 : F32)
    && ((Vec.y(q) - Vec.y(p) : F32) < 0.6 : F32))
  ((blade || ring) && U32.is_eq(inv, 0) && U32.is_eq(stun, 0) && (hp > 0.0 : F32))

# Does the strike a..b touch the boss: its hips (0.75), chest (0.8),
# head (0.62), shins (0.6), hands (0.45) or forearms (0.4)? The sword
# is no hurtbox.
def Boss.touch(+b: Boss, +a: Vec, +tip: Vec) -> Bool:
  Boss{p, _, face, _, stun, _, state, age, _, _, _} = b
  +k = Boss.pose(state, age, stun)
  +chest = Boss.at(p, face, Pose.spine(k, 0.57))
  +grip = Boss.hilt(p, face, k)
  ((Vec.seg(Boss.at(p, face, Pose.spine(k, 0.0)), a, tip) < 0.75 : F32)
    || (Vec.seg(chest, a, tip) < 0.8 : F32)
    || (Vec.seg(Boss.at(p, face, Pose.spine(k, 1.0)), a, tip) < 0.62 : F32)
    || (Vec.seg(Vec.add(p, Vec{0.0, 0.6, 0.0}), a, tip) < 0.6 : F32)
    || (Vec.seg(grip, a, tip) < 0.45 : F32)
    || (Vec.seg(Vec.mix(chest, grip, 0.5), a, tip) < 0.4 : F32))

# The damage of the hero's strike: on the tick its hit lands, when the
# needle's segment (reach 2.15, 2.7 a side, 3.8 a special) touches the
# boss, or a radial attack reaches its waist.
def Fighter.strike(+f: Fighter, +b: Boss) -> F32:
  Fighter{p, _, face, _, _, _, action, age, _, _, _, _, charge} = f
  Boss{q, _, _, _, _, _, _, _, _, _, _} = b
  +up = Act.up(action)
  +down = Act.down(action)
  +special = Act.special(action)
  +dx = (F32.cos(face) * Math.pick((up || down), 0.3,
    Math.pick(U32.is_eq(action, 15), (0.0 - 1.0 : F32), 1.0)) : F32)
  +dy = Math.pick(up, 1.0, Math.pick(down, (0.0 - 1.0 : F32), 0.1))
  +origin = Vec.add(p, Vec{0.0, 0.75, 0.0})
  +reach = Math.pick(special, 3.8, Math.pick(U32.is_eq(action, 10), 2.7, 2.15))
  +tip = Vec.add(origin, Vec.scale(Vec{dx, dy, 0.0}, reach))
  +near = (Boss.touch(b, origin, tip) || (Act.is(action, 13, 2, 23, 22)
    && (Vec.dist(origin, Vec.add(q, Vec{0.0, 1.6, 0.0})) < reach : F32)))
  +power = Math.pick(special, Math.pick(down, 32.0, 26.0),
    Math.pick(down, 18.0, Math.pick(up, 15.0, 13.0)))
  Math.pick((Act.attack(action) && U32.is_eq(age, Act.hit(action)) && near),
    (power * Act.power(charge) : F32), 0.0)

# A down air that hits bounces the hero and gives a jump back.
def Fighter.pogo(+f: Fighter, +hit: F32) -> Fighter:
  Fighter{p, v, face, damage, guard, jumps, action, age, inv, stocks, grace, queued, charge} = f
  +bounce = ((hit > 0.0 : F32) && U32.is_eq(action, 17))
  Fighter{p, Vec.mix(v, Vec{0.0, 0.39, 0.0}, Math.pick(bounce, 1.0, 0.0)), face, damage, guard,
    Math.word(bounce, 1, jumps), action, age, inv, stocks, grace, queued, charge}

# The hero struck by the boss: launched by his damage and the attack
# (hurt 23 ticks, invulnerable 48, the attack's damage), or, guarding
# over 24, nudged (guard -24, none on a parry; invulnerable 24).
def Fighter.impact(hit: Bool, +f: Fighter, +b: Boss) -> Fighter:
  match hit:
    case False{}:
      f
    case True{}:
      Fighter{p, _, face, damage, guard, jumps, action, age, _, stocks, grace, queued, charge} = f
      Boss{q, _, _, _, _, strain, state, _, _, _, _} = b
      +block = (U32.is_eq(action, 3) && (guard > 24.0 : F32))
      +parry = (block && (age <= 6 : U32))
      +power = Math.pick(block, 0.07, ((0.22 + damage * 0.0035) * Boss.push(state) : F32))
      +launch = Vec.add(Vec.scale(Vec.dir(q, p), power), Vec{0.0, Math.pick(block, 0.03, 0.29), 0.0})
      Fighter{p, launch, face, (damage + Math.pick(block, 0.0, Boss.blow(state)) : F32),
        Math.max(0.0, (guard - Math.pick(parry, 0.0, 24.0) : F32)), jumps,
        Math.word(block, action, 4), Math.word(block, age, 23), Math.word(block, 24, 48), stocks,
        grace, queued, charge}

# The boss struck for an amount, or parried (struck in the guard's
# first 6 ticks, guard over 24), or blocking: its vitality falls (22
# more on a parry), it is stunned (65 on a parry, else 10 plus the
# launch) out of its attack into a pause, launched by its strain, the
# charge and a special, and strained; a block starts the counter.
def Boss.hurt(+b: Boss, +amount: F32, +struck: Bool, +block: Bool, +f: Fighter) -> Boss:
  Boss{p, v, face, hp, stun, strain, state, age, hold, mark, gait} = b
  Fighter{q, _, _, _, guard, _, action, hage, _, _, _, _, charge} = f
  +parry = (struck && U32.is_eq(action, 3) && (hage <= 6 : U32) && (guard > 24.0 : F32))
  +hit = ((amount > 0.0 : F32) || parry)
  +power = ((0.11 + strain * 0.0016) * Act.power(charge)
    * Math.pick(Act.special(action), 1.4, 1.0) : F32)
  +lift = Math.pick(Act.up(action), 0.85, Math.pick(Act.down(action), (0.0 - 0.65 : F32), 0.40))
  +launch = Vec.add(Vec.scale(Vec.dir(q, p), power), Vec{0.0, (lift * power : F32), 0.0})
  +daze = Math.word(parry, 65, Math.word(hit, (10 + F32.to_u32((power * 32.0 : F32)) : U32), stun))
  Boss{p, Vec.mix(v, launch, Math.pick(hit, 1.0, 0.0)), face,
    Math.max(0.0, (hp - amount - Math.pick(parry, 22.0, 0.0) : F32)), daze,
    (strain + amount * 0.85 + Math.pick(parry, 18.0, 0.0) : F32),
    Math.word(hit, 0, Math.word(block, 6, state)), Math.word((hit || block), 0, age),
    Math.word(hit, (daze + 15 : U32), hold), mark, gait}

# Does the boss block the strike: in its stalk past its pause, not
# stunned, three times in eight?
def Boss.blocks(+b: Boss, +amount: F32, +t: U32) -> Bool:
  Boss{_, _, _, _, stun, _, state, age, hold, _, _} = b
  ((amount > 0.0 : F32) && U32.is_eq(state, 0) && U32.is_eq(stun, 0) && (age >= hold : U32)
    && ((Boss.hash(t) .&. 7 : U32) < 3 : U32))

def Fighter.out(+f: Fighter) -> Bool:
  Fighter{p, _, _, _, _, _, _, _, _, _, _, _, _} = f
  Vec.out(p)

def Boss.dead(+b: Boss) -> Bool:
  Boss{_, _, _, hp, _, _, _, _, _, _, _} = b
  (hp <= 0.0 : F32)

# A life spent: a respawn at (-2.8, 4) invulnerable 120 ticks, or, on
# the last, dead where he fell.
def Fighter.spend(more: Bool, +f: Fighter) -> Fighter:
  match more:
    case True{}:
      Fighter{p, v, face, damage, guard, jumps, action, age, inv, stocks, grace, queued, charge} = f
      Fighter.spawn(Vec{(0.0 - 2.8 : F32), 4.0, 0.0}, (stocks - 1 : U32), 120)
    case False{}:
      Fighter{p, v, face, damage, guard, jumps, action, age, inv, _, grace, queued, charge} = f
      Fighter{p, v, face, damage, guard, jumps, action, age, inv, 0, grace, queued, charge}

def Fighter.life(out: Bool, +f: Fighter) -> Fighter:
  match out:
    case False{}:
      f
    case True{}:
      Fighter{_, _, _, _, _, _, _, _, _, stocks, _, _, _} = f
      Fighter.spend((stocks > 1 : U32), f)

# The hero at rest after a win or a loss.
def Fighter.rest(done: Bool, +f: Fighter) -> Fighter:
  match done:
    case False{}:
      f
    case True{}:
      Fighter{p, _, face, damage, guard, jumps, _, _, _, stocks, grace, queued, charge} = f
      Fighter{p, Vec{0.0, 0.0, 0.0}, face, damage, guard, jumps, 0, 0, 0, stocks, grace, queued, charge}

# The cape after a tick: kept (paused), seeded at the hero (a respawn),
# or stepped about his shoulders, lowered in a crouch.
def Game.cape(keep: Bool, reset: Bool, cloth: Cloth, +f: Fighter, +time: U32) -> Cloth:
  match keep reset:
    case True{} _:
      cloth
    case False{} True{}:
      Fighter{p, v, face, damage, guard, jumps, action, age, inv, stocks, grace, queued, charge} = f
      Cloth.seed(3n, 0, Fit.cape(), p, face)
    case False{} False{}:
      Fighter{p, _, face, _, _, _, action, _, _, _, _, _, _} = f
      Cloth.step(cloth, Fit.cape(), p, face, U32.to_f32(time), (Act.crouch(action) * 0.3 : F32))

# The boss's cloths after a tick: kept (paused), or stepped about its
# anchor.
def Game.garb(keep: Bool, +g: Garb, +b: Boss, +time: U32) -> Garb:
  match keep:
    case True{}:
      g
    case False{}:
      Boss{_, _, face, _, _, _, _, _, _, _, _} = b
      Garb.step(g, Boss.anchor(b), face, U32.to_f32(time))

# The lens after the hero and the boss (the hero alone once the boss
# is dead).
def Game.follow(+l: Lens, +f: Fighter, +b: Boss) -> Lens:
  Fighter{p, v, face, _, _, _, _, _, _, _, _, _, _} = f
  Vec{px, py, _} = p
  Vec{vx, vy, _} = v
  Boss{q, _, yaw, hp, _, _, _, _, _, _, _} = b
  Vec{bx, by, _} = q
  +dead = (hp <= 0.0 : F32)
  Lens.follow(l, px, py, vx, vy, Math.pick(dead, px, bx), Math.pick(dead, py, by),
    Math.pick(dead, face, yaw))

# The detonation after a tick: the hero's where he fell out, the boss's
# where it died, else the last.
def Game.blast(
  out: Bool, killed: Bool, old: Maybe<&2, Blast>, +f: Fighter, +b: Boss, +time: U32
) -> Maybe<&2, Blast>:
  match out killed:
    case True{} _:
      Fighter{p, v, face, _, _, _, _, age, _, _, _, _, _} = f
      Vec{x, y, z} = p
      Some{Blast{x, y, time, 1}}
    case False{} True{}:
      Boss{p, _, _, _, _, _, _, _, _, _, _} = b
      Vec{x, y, _} = p
      Some{Blast{x, y, time, 2}}
    case False{} False{}:
      old

# The mode after a tick: 3 with the hero's lives out, 2 with the boss's
# vitality, once its detonation (42 ticks) is over, else 1.
def Game.outcome(+f: Fighter, +b: Boss, blast: Maybe<&2, Blast>, +time: U32) -> U32:
  Fighter{_, _, _, _, _, _, _, _, _, stocks, _, _, _} = f
  Boss{_, _, _, hp, _, _, _, _, _, _, _} = b
  Math.word(U32.is_eq(stocks, 0), 3, Math.word(((hp <= 0.0 : F32) && Blast.over(blast, time)), 2, 1))

# A tick of the fight: the hero and the boss move, the boss's hit and
# the hero's strike land (or the boss blocks it), the hero is launched
# (or pogos), falls out and respawns, the boss is hurt; a death
# detonates; a hit flashes 7; the cloths, the lens.
def Game.fight(+g: Game) -> Game:
  Game{time, held, taps, _, hero, boss, flash, cloth, garb, lens, blast} = g
  +p = Fighter.tick(hero, held, taps)
  +b = Boss.tick(boss, p, time)
  +hit = Boss.contact(p, b)
  +raw = Fighter.strike(p, b)
  +blocked = Boss.blocks(b, raw, time)
  +dmg = Math.pick(blocked, 0.0, raw)
  +hurt = Fighter.pogo(Fighter.impact(hit, p, b), dmg)
  +out = Fighter.out(hurt)
  +next = Fighter.life(out, hurt)
  +enemy = Boss.hurt(b, dmg, hit, blocked, p)
  +boom = Game.blast(out, (Boss.dead(enemy) && Bool.not(Boss.dead(boss))), blast, hurt, enemy,
    time)
  Game{(time + 1 : U32), held, 0, Game.outcome(next, enemy, boom, (time + 1 : U32)), next,
    enemy, Math.word((hit || blocked || (dmg > 0.0 : F32)), 7, Sim.dec(flash)),
    Game.cape(False{}, out, cloth, next, time), Game.garb(False{}, garb, enemy, time),
    Game.follow(lens, next, enemy), boom}

# A tick out of the fight: the time runs and the cape settles unless
# paused, the hero rests after a win or a loss, the flash fades.
def Game.rest(+g: Game) -> Game:
  Game{time, held, taps, mode, hero, boss, flash, cloth, garb, lens, blast} = g
  +paused = U32.is_eq(mode, 4)
  Game{Math.word(paused, time, (time + 1 : U32)), held, 0, mode,
    Fighter.rest((U32.is_eq(mode, 2) || U32.is_eq(mode, 3)), hero), boss, Sim.dec(flash),
    Game.cape(paused, False{}, cloth, hero, time), Game.garb(paused, garb, boss, time), lens,
    blast}

# A tick of hitstop: the world holds, the taps too; the flash fades.
def Game.freeze(+g: Game) -> Game:
  Game{time, held, taps, mode, hero, boss, flash, cloth, garb, lens, blast} = g
  Game{(time + 1 : U32), held, taps, mode, hero, boss, Sim.dec(flash), cloth, garb, lens, blast}

# P (or L in a pause) toggles the fight and the pause.
def Game.pause(+g: Game) -> Game:
  Game{time, held, _, mode, hero, boss, flash, cloth, garb, lens, blast} = g
  Game{time, held, 0, Math.word(U32.is_eq(mode, 4), 1, Math.word(U32.is_eq(mode, 1), 4, mode)),
    hero, boss, flash, cloth, garb, lens, blast}

# The tick by the keys: K past the fight goes back to the title; R, or
# L outside the fight and the pause, starts a fresh fight; P toggles
# the pause; the fight runs, or holds in hitstop; the rest rests.
def Game.route(back: Bool, fresh: Bool, pause: Bool, live: Bool, frozen: Bool, +g: Game) -> Game:
  match back fresh pause live frozen:
    case True{} _ _ _ _:
      Game.init()
    case False{} True{} _ _ _:
      Game{_, held, _, _, _, _, _, _, _, _, _} = g
      Game.fresh(held, 1)
    case False{} False{} True{} _ _:
      Game.pause(g)
    case False{} False{} False{} True{} False{}:
      Game.fight(g)
    case False{} False{} False{} True{} True{}:
      Game.freeze(g)
    case False{} False{} False{} False{} _:
      Game.rest(g)

def Game.step(+g: Game) -> Game:
  Game{_, _, taps, mode, _, _, flash, _, _, _, _} = g
  Game.route((Sim.has(taps, 32) && (mode >= 2 : U32)),
    (Sim.has(taps, 512) || (Sim.has(taps, 128) && Bool.not(U32.is_eq(mode, 1))
      && Bool.not(U32.is_eq(mode, 4)))),
    (Sim.has(taps, 1024) || (U32.is_eq(mode, 4) && Sim.has(taps, 128))), U32.is_eq(mode, 1),
    (flash >= 6 : U32), g)

# Hero
# ----

# The needle's angle: a swing over the attack's progress (raised for
# an upward attack, straight down for a downward one, reversed for a
# back air), 2.2 while charging, -0.32 at rest.
def Hero.angle(+act: U32, +age: U32) -> F32:
  +len = U32.to_f32(Act.length(act))
  +u = Math.sat(((len - U32.to_f32(age)) / len : F32))
  +swing = Math.mix(1.8, (0.0 - 0.8 : F32), Math.smooth((u * 2.5 : F32)))
  Math.pick(Act.in(act, 30, 32), 2.2, Math.pick(Act.attack(act),
    Math.pick(Act.up(act), (swing + 1.25 : F32), Math.pick(Act.down(act),
      (0.0 - 1.57 : F32), Math.pick(U32.is_eq(act, 15), (swing + 3.14 : F32), swing))),
    (0.0 - 0.32 : F32)))

# A part of the hero: a surface in his frame, turned to his facing at
# his feet.
def Hero.part(
  s: Surf, +mat: Mat, +nu: U32, +nv: U32, +at: Vec, +face: F32, +cam: Cam
) -> Cells:
  Mesh.of(Surf.turn(s, at, face), mat, nu, nv, cam)

# A leg: hip to knee to foot, swung by the stride, lifted in the air,
# folded in a crouch, tucked in a dodge; a bead at the knee and the
# foot.
def Hero.leg(
  +stride: F32, +side: F32, +air: F32, +crouch: F32, +dodge: F32, +at: Vec,
  +face: F32, +cam: Cam
) -> Cells:
  +hip = {Vec{0.0, (0.69 - crouch * 0.28 : F32), (side * 0.10 : F32)} : Vec}
  +knee = {Vec{(stride * 0.45 + air * 0.15 + crouch * 0.20 : F32),
    (0.39 + F32.abs(stride) * 0.20 + air * 0.15 - crouch * 0.12 + dodge * 0.16 : F32),
    (side * 0.13 : F32)} : Vec}
  +foot = {Vec{(stride - air * side * 0.18 - crouch * 0.12 : F32),
    (0.045 + Math.max(0.0, (stride * side : F32)) * 0.4 + air * 0.17 + dodge * 0.36 : F32),
    (side * 0.14 : F32)} : Vec}
  a b c d = Hero.part(Inst.span(Tube{}, hip, knee, 0.062, 0.062), Mat.bone(2039592),
      8, 2, at, face, cam)
    Hero.part(Inst.span(Tube{}, knee, foot, 0.043, 0.043), Mat.bone(3226700), 8, 2,
      at, face, cam)
    Hero.part(Inst.ball(Globe{}, knee, 0.066, 0.060, 0.060), Mat.bead(1320230, 0.0),
      8, 4, at, face, cam)
    Hero.part(Inst.ball(Globe{}, Vec.add(foot, Vec{0.04, 0.0, 0.0}), 0.12, 0.044,
      0.052), Mat.bead(1519151, 0.0), 8, 4, at, face, cam)
  Cells.m4(a, b, c, d)

# A horn of the crown on a side of the mask at (hx, hy), and an eye on
# the side seen (z) at x.
def Hero.horn(
  +side: F32, +hx: F32, +hy: F32, +shell: Mat, +at: Vec, +face: F32, +cam: Cam
) -> Cells:
  Hero.part(Inst.span(Horn{}, Vec{(hx + side * 0.17 : F32), (hy + 0.13 : F32), 0.0},
    Vec{(hx + side * 0.24 : F32), (hy + 0.62 : F32), 0.0}, 0.60, 0.55), shell, 8, 4,
    at, face, cam)

def Hero.eye(+x: F32, +hy: F32, +z: F32, +at: Vec, +face: F32, +cam: Cam) -> Cells:
  Hero.part(Inst.ball(Globe{}, Vec{x, (hy + 0.014 : F32), z}, 0.044, 0.082, 0.024),
    Mat.bead(593179, 0.0), 8, 4, at, face, cam)

# The mask (white, or flashing) at (hx, hy) with its two horns, its
# chin and the two eyes on the side seen.
def Hero.head(
  +hx: F32, +hy: F32, +white: U32, +at: Vec, +face: F32, +cam: Cam
) -> Cells:
  +shell = Mat.paint(white, 0.46, 0.02, 0.0)
  +side = Math.pick((F32.cos(face) >= 0.0 : F32), 0.184, (0.0 - 0.184 : F32))
  a b c d e f = Hero.part(Inst.ball(Globe{}, Vec{hx, hy, 0.0}, 0.235, 0.28, 0.21), shell,
      16, 8, at, face, cam)
    Hero.horn(1.0, hx, hy, shell, at, face, cam)
    Hero.horn((0.0 - 1.0 : F32), hx, hy, shell, at, face, cam)
    Hero.part(Inst.ball(Globe{}, Vec{hx, (hy - 0.20 : F32), 0.0}, 0.13, 0.13, 0.13),
      shell, 8, 4, at, face, cam)
    Hero.eye((hx + 0.087 : F32), hy, side, at, face, cam)
    Hero.eye((hx - 0.087 : F32), hy, side, at, face, cam)
  Cells.merge(Cells.m4(a, b, c, d), Cells.merge(e, f))

# The arm to the hand, the needle from the hand at its angle (glowing
# when charged), the hand's bead and the grip behind it.
def Hero.needle(
  +lean: F32, +crouch: F32, +theta: F32, +white: U32, +charge: U32, +at: Vec,
  +face: F32, +cam: Cam
) -> Cells:
  +ct = F32.cos(theta)
  +st = F32.sin(theta)
  +hand = {Vec{(0.22 + ct * 0.16 : F32), (0.92 + st * 0.14 - crouch * 0.3 : F32), 0.24} : Vec}
  +hot = (charge > 10 : U32)
  a b c d = Hero.part(Inst.span(Tube{}, Vec{lean, (1.02 - crouch * 0.30 : F32), 0.12},
      hand, 0.045, 0.045), Mat.bone(1185307), 8, 2, at, face, cam)
    Hero.part(Inst.span(Blade{}, hand, Vec.add(hand, Vec{(ct * 1.65 : F32),
      (st * 1.65 : F32), 0.0}), 0.62, 0.6), Mat.paint(Math.word(hot, 16768443, 15071203),
      0.16, 0.88, Math.pick(hot, 0.18, 0.0)), 8, 8, at, face, cam)
    Hero.part(Inst.ball(Globe{}, hand, 0.061, 0.064, 0.050), Mat.bead(white, 0.0), 8, 4,
      at, face, cam)
    Hero.part(Inst.span(Tube{}, Vec.sub(hand, Vec{(ct * 0.18 : F32), (st * 0.18 : F32),
      0.0}), hand, 0.032, 0.032), Mat.bone(6774368), 8, 2, at, face, cam)
  Cells.m4(a, b, c, d)

# The hero at a time: his body and mask over the legs (a run cycle by
# his speed, lifted in the air, folded in a crouch), leaning into his
# motion, the needle at its angle, his shadow.
def Hero.build(+f: Fighter, +t: F32, +cam: Cam) -> Cells:
  Fighter{p, v, face, _, _, _, act, age, inv, _, _, _, charge} = f
  Vec{x, y, _} = p
  Vec{vx, _, _} = v
  +air = Math.pick(Fighter.air(p, v), 1.0, 0.0)
  +crouch = Act.crouch(act)
  +dodge = Math.pick(U32.is_eq(act, 6), 1.0, 0.0)
  +run = (F32.sin((t * 0.28 : F32)) * Math.min(1.0, (F32.abs(vx) * 5.0 : F32)) * 0.38
    * (1.0 - air) : F32)
  +lean = (vx * F32.cos(face) * 0.26 + crouch * 0.07 : F32)
  +white = Math.word(((inv > 0) && ((inv .&. 4) > 0) : U32), 13036021, 15790567)
  b a c d e g = Hero.head(lean, (1.34 - crouch * 0.30 + F32.abs(run) * 0.04 : F32), white, p,
      face, cam)
    Hero.part(Inst.ball(Globe{}, Vec{lean, (0.88 - crouch * 0.30 : F32), 0.0}, 0.13, 0.30, 0.115),
      Mat.paint(987159, 0.6, 0.0, 0.0), 12, 8, p, face, cam)
    Hero.leg(run, 1.0, air, crouch, dodge, p, face, cam)
    Hero.leg((0.0 - run : F32), (0.0 - 1.0 : F32), air, crouch, dodge, p, face, cam)
    Hero.needle(lean, crouch, Hero.angle(act, age), white, charge, p, face, cam)
    Shadow.build(x, y, 0.70, cam)
  Cells.merge(Cells.m4(a, b, c, d), Cells.merge(e, g))

# Boss
# ----

# The boss's cloth (blue-black), its bone (the mask), its steel.
def Boss.cloth() -> Mat:
  Mat.paint(922660, 0.85, 0.0, 0.0)

# A leg: hip to knee to foot, swung by the stride, lifted in the air,
# folded by the dip.
def Boss.leg(
  +stride: F32, +side: F32, +air: F32, +dip: F32, +at: Vec, +face: F32, +cam: Cam
) -> Cells:
  +hip = {Vec{0.05, (1.75 - dip : F32), (side * 0.30 : F32)} : Vec}
  +knee = {Vec{(stride * 0.9 + air * 0.3 + dip * 0.55 : F32),
    (0.92 + F32.abs(stride) * 0.25 + air * 0.35 - dip * 0.45 : F32), (side * 0.34 : F32)} : Vec}
  +foot = {Vec{(stride * 1.5 - air * side * 0.3 - dip * 0.2 : F32),
    (0.1 + Math.max(0.0, (stride * side : F32)) * 0.7 + air * 0.4 : F32), (side * 0.36 : F32)} : Vec}
  a b c = Hero.part(Inst.span(Tube{}, hip, knee, 0.17, 0.17), Boss.cloth(), 8, 2, at, face, cam)
    Hero.part(Inst.span(Tube{}, knee, foot, 0.13, 0.13), Boss.cloth(), 8, 2, at, face, cam)
    Hero.part(Inst.ball(Globe{}, Vec.add(foot, Vec{0.14, 0.0, 0.0}), 0.30, 0.09, 0.14),
      Mat.bone(1778496), 8, 4, at, face, cam)
  Cells.merge(a, Cells.merge(b, c))

# An arm from the shoulder (a ball) to the hand, bent at the elbow
# (out of the line, in the combat plane; 0.95 a bone).
def Boss.arm(+shoulder: Vec, +hand: Vec, +at: Vec, +face: F32, +cam: Cam) -> Cells:
  +span = Vec.sub(hand, shoulder)
  +half = (Vec.len(span) * 0.5 : F32)
  +elbow = Vec.add(Vec.mix(shoulder, hand, 0.5), Vec.scale(Vec.unit(Vec.cross(span, Vec{0.0, 0.0, 1.0})),
    F32.sqrt(Math.max(0.0, (0.9025 - half * half : F32)))))
  a b c d = Hero.part(Inst.span(Tube{}, shoulder, elbow, 0.14, 0.14), Boss.cloth(), 8, 2, at, face, cam)
    Hero.part(Inst.span(Tube{}, elbow, hand, 0.11, 0.11), Boss.cloth(), 8, 2, at, face, cam)
    Hero.part(Inst.ball(Globe{}, shoulder, 0.27, 0.24, 0.27), Boss.cloth(), 8, 4, at, face, cam)
    Hero.part(Inst.ball(Globe{}, hand, 0.13, 0.11, 0.11), Mat.bone(1778496), 8, 4, at, face, cam)
  Cells.m4(a, b, c, d)

# The katana at the grip g along d: the blade (3.1, curving toward its
# right), the glowing edge along its convex side (two tubes), the
# guard, the wrapped hilt, the pommel.
def Boss.sword(+g: Vec, +d: Vec, +at: Vec, +face: F32, +cam: Cam) -> Cells:
  +right = Vec.unit(Vec.cross(d, Vec{0.002, 0.0, 1.0}))
  +tip = Vec.add(g, Vec.scale(d, 3.1))
  +mid = Vec.add(g, Vec.scale(d, 1.6))
  +edge = Mat.paint(10352639, 0.3, 0.0, 1.4)
  +root = Vec.add(Vec.add(g, Vec.scale(d, 0.2)), Vec.scale(right, (0.0 - 0.09 : F32)))
  +point = Vec.add(Vec.add(tip, Vec.scale(d, (0.0 - 0.08 : F32))), Vec.scale(right, 0.27))
  a b c dd e f = Hero.part(Inst.span(Blade{}, g, tip, 1.5, 1.5), Mat.paint(13161184, 0.18, 0.9, 0.0),
      8, 8, at, face, cam)
    Hero.part(Inst.span(Tube{}, root, mid, 0.022, 0.022), edge, 4, 1, at, face, cam)
    Hero.part(Inst.span(Tube{}, mid, point, 0.022, 0.022), edge, 4, 1, at, face, cam)
    Hero.part(Inst.of(Globe{}, g, Vec.scale(right, 0.24), Vec.scale(d, 0.035),
      Vec.scale(Vec.cross(d, right), 0.24)), Mat.paint(1778496, 0.4, 0.6, 0.0), 8, 4, at, face, cam)
    Hero.part(Inst.span(Tube{}, Vec.sub(g, Vec.scale(d, 0.62)), g, 0.055, 0.055),
      Mat.paint(1778496, 0.6, 0.2, 0.0), 6, 1, at, face, cam)
    Hero.part(Inst.ball(Globe{}, Vec.sub(g, Vec.scale(d, 0.62)), 0.075, 0.075, 0.075),
      Mat.paint(13161184, 0.3, 0.8, 0.0), 6, 3, at, face, cam)
  Cells.merge(Cells.m4(a, b, c, dd), Cells.merge(e, f))

# A point on the mask (an ellipsoid of 0.42, 0.46, 0.34 about the head,
# 0.05 ahead) at (x, y) on its side z (1 or -1), lifted by h.
def Boss.mask(+head: Vec, +x: F32, +y: F32, +z: F32, +h: F32) -> Vec:
  Vec.add(head, Vec{(x + 0.05 : F32), y, (z * ((0.34 + h) * F32.sqrt(Math.max(0.0,
    (1.0 - (x * x) / 0.1764 - (y * y) / 0.2116 : F32))) : F32) : F32)})

# The head: the hood (dark, behind and over), the pale mask before it,
# a crack down the mask's side seen (two dark threads on its surface),
# a glowing slit eye on each side (red when enraged).
def Boss.head(+head: Vec, +hot: Bool, +at: Vec, +face: F32, +cam: Cam) -> Cells:
  +eye = Mat.paint(Math.word(hot, 16726560, 2152703), 0.3, 0.0, 3.0)
  +dark = Mat.paint(659473, 0.9, 0.0, 0.0)
  +side = Math.pick((F32.cos(face) >= 0.0 : F32), 1.0, (0.0 - 1.0 : F32))
  +top = Boss.mask(head, 0.06, 0.40, side, 0.01)
  +knot = Boss.mask(head, (0.0 - 0.02 : F32), 0.04, side, 0.01)
  +chin = Boss.mask(head, 0.16, (0.0 - 0.26 : F32), side, 0.01)
  a b c d e f = Hero.part(Inst.ball(Globe{}, Vec.add(head, Vec{(0.0 - 0.32 : F32), 0.14, 0.0}),
      0.52, 0.58, 0.50), dark, 10, 5, at, face, cam)
    Hero.part(Inst.ball(Globe{}, Vec.add(head, Vec{0.05, 0.0, 0.0}), 0.42, 0.46, 0.34),
      Mat.paint(15131350, 0.42, 0.05, 0.0), 12, 8, at, face, cam)
    Hero.part(Inst.span(Tube{}, top, knot, 0.016, 0.016), dark, 4, 1, at, face, cam)
    Hero.part(Inst.span(Tube{}, knot, chin, 0.016, 0.016), dark, 4, 1, at, face, cam)
    Hero.part(Inst.ball(Globe{}, Boss.mask(head, 0.2, 0.1, 1.0, 0.0), 0.17, 0.065, 0.05),
      eye, 6, 3, at, face, cam)
    Hero.part(Inst.ball(Globe{}, Boss.mask(head, 0.2, 0.1, (0.0 - 1.0 : F32), 0.0), 0.17,
      0.065, 0.05), eye, 6, 3, at, face, cam)
  Cells.merge(Cells.m4(a, b, c, d), Cells.merge(e, f))

# The trunk: hips to chest, the chest, the hips, the neck.
def Boss.trunk(+hips: Vec, +chest: Vec, +head: Vec, +p: Vec, +face: F32, +cam: Cam) -> Cells:
  a b c d = Hero.part(Inst.span(Tube{}, hips, chest, 0.36, 0.30), Boss.cloth(), 10, 2, p, face, cam)
    Hero.part(Inst.ball(Globe{}, chest, 0.46, 0.50, 0.38), Boss.cloth(), 10, 5, p, face, cam)
    Hero.part(Inst.ball(Globe{}, hips, 0.38, 0.32, 0.32), Boss.cloth(), 10, 5, p, face, cam)
    Hero.part(Inst.span(Tube{}, chest, head, 0.13, 0.13), Boss.cloth(), 6, 1, p, face, cam)
  Cells.m4(a, b, c, d)

# The body at a pose: the trunk, the head, the legs (a stride, tucked
# in the air), the arms to the two-handed grip, the katana, the cloths,
# the shadow.
def Boss.body(
  +p: Vec, +face: F32, +k: Pose, +stride: F32, +air: F32, +hot: Bool, +garb: Garb, +cam: Cam
) -> Cells:
  Vec{bx, by, _} = p
  Pose{_, _, _, _, _, dip, lean} = k
  +hips = Pose.spine(k, 0.0)
  +chest = Pose.spine(k, 0.57)
  +head = Pose.spine(k, 1.0)
  +grip = Pose.grip(k)
  +d = Pose.dir(k)
  +sy = (3.1 - dip * 1.12 : F32)
  +sx = (lean * 0.75 : F32)
  l a e f g h i j m = Garb.build(garb, cam) Boss.trunk(hips, chest, head, p, face, cam)
    Boss.head(head, hot, p, face, cam)
    Boss.leg(stride, 1.0, air, dip, p, face, cam)
    Boss.leg((0.0 - stride : F32), (0.0 - 1.0 : F32), air, dip, p, face, cam)
    Boss.sword(grip, d, p, face, cam)
    Boss.arm(Vec{sx, sy, 0.55}, Vec.add(grip, Vec{0.0, 0.0, 0.12}), p, face, cam)
    Boss.arm(Vec{sx, sy, (0.0 - 0.55 : F32)},
      Vec.sub(grip, Vec.add(Vec.scale(d, 0.4), Vec{0.0, 0.0, 0.12})), p, face, cam)
    Shadow.build(bx, by, 1.6, cam)
  Cells.merge(a, Cells.merge(Cells.m4(e, f, g, h), Cells.m4(i, j, l, m)))

def Boss.alive(dead: Bool, +b: Boss, +garb: Garb, +t: F32, +cam: Cam) -> Cells:
  match dead:
    case True{}:
      CNil{}
    case False{}:
      Boss{p, v, face, hp, stun, _, state, age, _, _, gait} = b
      Boss.body(p, face, Boss.pose(state, age, stun),
        (F32.sin((t * 0.14 : F32)) * Math.min(1.0, (F32.abs(gait) * 16.0 : F32)) * 0.55 : F32),
        Math.pick(Fighter.air(p, v), 1.0, 0.0), (hp < 160.0 : F32), garb, cam)

# The boss at a time: its pose by its state and age (reeling when
# stunned), a stride by its gait, its eyes red when enraged; dead, its
# detonation stands for it.
def Boss.build(+b: Boss, +garb: Garb, +t: F32, +cam: Cam) -> Cells:
  Boss.alive(Boss.dead(b), b, garb, t, cam)

# View
# ----

# An angle u of the way from a to b, the short way round.
def Math.turn(+a: F32, +b: F32, +u: F32) -> F32:
  (a + F32.atan2(F32.sin((b - a : F32)), F32.cos((b - a : F32))) * u : F32)

# The hero u of the way between two ticks; snapped when a life was lost
# or he moved 2 or more (a respawn).
def Fighter.lerp(+a: Fighter, +b: Fighter, +u: F32) -> Fighter:
  Fighter{p0, v0, f0, _, _, _, _, _, _, s0, _, _, _} = a
  Fighter{p, v, face, damage, guard, jumps, action, age, inv, stocks, grace, queued, charge} = b
  +k = Math.pick((U32.is_eq(s0, stocks) && (Vec.dist(p0, p) < 2.0 : F32)), u, 1.0)
  Fighter{Vec.mix(p0, p, k), Vec.mix(v0, v, k), Math.turn(f0, face, k), damage, guard, jumps,
    action, age, inv, stocks, grace, queued, charge}

def Boss.lerp(+a: Boss, +b: Boss, +u: F32) -> Boss:
  Boss{p0, _, f0, _, _, _, _, _, _, _, _} = a
  Boss{p, v, face, hp, stun, strain, state, age, hold, mark, gait} = b
  Boss{Vec.mix(p0, p, u), v, Math.turn(f0, face, u), hp, stun, strain, state, age, hold, mark, gait}

def Lens.lerp(+a: Lens, +b: Lens, +u: F32) -> Lens:
  Lens{x0, y0, w0, _, _, _} = a
  Lens{x, y, w, vx, vy, vw} = b
  Lens{Math.mix(x0, x, u), Math.mix(y0, y, u), Math.mix(w0, w, u), vx, vy, vw}

def Fighter.at(+f: Fighter) -> Vec:
  Fighter{p, _, _, _, _, _, _, _, _, _, _, _, _} = f
  p

# The game u of the way from tick a to tick b for the view; the cape
# snaps when the hero moved 2 or more.
def Game.lerp(+a: Game, +b: Game, +u: F32) -> Game:
  Game{_, _, _, _, p0, b0, _, c0, r0, l0, _} = a
  Game{time, held, taps, mode, hero, boss, flash, cloth, garb, lens, blast} = b
  +snap = (Vec.dist(Fighter.at(p0), Fighter.at(hero)) >= 2.0 : F32)
  Game{time, held, taps, mode, Fighter.lerp(p0, hero, u), Boss.lerp(b0, boss, u), flash,
    Cloth.lerp(c0, cloth, Math.pick(snap, 1.0, u)), Garb.lerp(r0, garb, u), Lens.lerp(l0, lens, u),
    blast}

# The view's clock: the tick and the way to the next, held in a pause.
def Game.clock(+g: Game, +u: F32) -> F32:
  Game{time, _, _, mode, _, _, _, _, _, _, _} = g
  Math.pick(U32.is_eq(mode, 4), U32.to_f32(time),
    Math.max(0.0, (U32.to_f32(time) - 1.0 + u : F32)))

# A point on a sphere of radius r at c toward s, and the nearer of two
# points to s.
def Vec.onto(+c: Vec, +r: F32, +s: Vec) -> Vec:
  Vec.mix(c, s, Math.min(1.0, (r / Math.max(0.001, Vec.dist(c, s)) : F32)))

def Vec.nearer(+a: Vec, +b: Vec, +s: Vec) -> Vec:
  Vec.mix(a, b, Math.pick((Vec.dist(b, s) < Vec.dist(a, s) : F32), 1.0, 0.0))

# The contact point (the flash's light): the point of the boss's chest
# or head nearest the hero's chest while he attacks, else the chest.
def Game.contact(+f: Fighter, +b: Boss) -> Vec:
  Fighter{p, _, _, _, guard, _, action, _, _, _, _, _, charge} = f
  Boss{q, _, yaw, _, stun, _, state, bage, _, _, _} = b
  +k = Boss.pose(state, bage, stun)
  +s = Vec.add(p, Vec{0.0, 0.9, 0.16})
  +on = Vec.nearer(Vec.onto(Boss.at(q, yaw, Pose.spine(k, 0.57)), 0.8, s),
    Vec.onto(Boss.at(q, yaw, Pose.spine(k, 1.0)), 0.5, s), s)
  Vec.mix(s, on, Math.pick(Act.attack(action), 1.0, 0.0))

# Effects
# -------

# The effects of the view's state, records drawn after: the swing's
# arcs while its hit is near, a special's ribbons over its progress,
# the smash charge's glow, the air dodge's ring, the guard's field,
# the sparks of a flash at the contact point, a death's detonation
# (inside the lens), the boss's blade trail, its slam's shockwave,
# its block's flash and its enraged aura.
type Fx is Data:
  Swing{p: Vec, face: F32, angle: F32, charge: U32}
  Special{p: Vec, face: F32, act: U32, u: F32}
  Charge{p: Vec, face: F32, u: F32, t: F32}
  Dodge{p: Vec, face: F32, age: U32}
  Guard{p: Vec, guard: F32, age: U32, flash: U32}
  Spark{p: Vec, age: U32}
  Boom{x: F32, y: F32, age: F32, who: U32}
  Slash{p: Vec, face: F32, state: U32, age: U32, stun: U32}
  Shock{x: F32, y: F32, age: U32}
  Parry{p: Vec, age: U32}
  Aura{p: Vec, t: F32}

# A quad of projected corners, one colour blended (m 1 alpha, 2
# additive) at al, in the cells; behind the eye, nothing.
def Fx.put(
  +a: Vec, +b: Vec, +c: Vec, +d: Vec, +col: U32, +m: U32, +al: F32, cells: Cells
) -> Cells:
  Vec{ax, ay, aw} = a
  Vec{bx, by, _} = b
  Vec{cx, cy, cw} = c
  Vec{dx, dy, _} = d
  Quad.put(ax, ay, bx, by, cx, cy, dx, dy, Math.min(aw, cw), col, m, al, cells)

def Fx.quad(
  +a: Vec, +b: Vec, +c: Vec, +d: Vec, +col: U32, +m: U32, +al: F32, +cam: Cam,
  cells: Cells
) -> Cells:
  Fx.put(Cam.proj(cam, a), Cam.proj(cam, b), Cam.proj(cam, c), Cam.proj(cam, d), col, m,
    al, cells)

# An additive beam from a to b, w0 wide at a and w1 at b, its width
# across z (facing the eye).
def Fx.beam(
  +a: Vec, +b: Vec, +w0: F32, +w1: F32, +col: U32, +al: F32, +cam: Cam, cells: Cells
) -> Cells:
  +n = Vec.unit(Vec.cross(Vec.sub(b, a), Vec{0.0, 0.0, 1.0}))
  Fx.quad(Vec.add(a, Vec.scale(n, w0)), Vec.add(b, Vec.scale(n, w1)),
    Vec.sub(b, Vec.scale(n, w1)), Vec.sub(a, Vec.scale(n, w0)), col, 2, al, cam, cells)

# A point of an arc: at an angle on a circle of radius r about the
# chest (0.90 up, 0.34 before) of a figure at p facing face.
def Fx.arcpt(+ang: F32, +r: F32, +p: Vec, +face: F32) -> Vec:
  Boss.at(p, face, Vec{(F32.cos(ang) * r : F32), (0.90 + F32.sin(ang) * r : F32), 0.34})

# n segments of an additive arc from segment i (each k of the way):
# from theta over sweep at a radius, its width inward swelling as
# sin(pi u).
def Fx.arc(
  n: Nat, +i: F32, +k: F32, +theta: F32, +sweep: F32, +r: F32, +width: F32, +p: Vec,
  +face: F32, +col: U32, +al: F32, +cam: Cam, acc: Cells
) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +u = (i * k : F32)
      +a = (theta + u * sweep : F32)
      +b = (theta + (u + k) * sweep : F32)
      +w = (r - width * F32.sin((u * 3.1415927 : F32)) : F32)
      Fx.arc(m, (i + 1.0 : F32), k, theta, sweep, r, width, p, face, col, al, cam,
        Fx.quad(Fx.arcpt(a, r, p, face), Fx.arcpt(b, r, p, face), Fx.arcpt(b, w, p, face),
          Fx.arcpt(a, w, p, face), col, 2, al, cam, acc))

# n triangles from i of an additive disc about c facing the eye.
def Fx.disc(
  n: Nat, +i: F32, +k: F32, +c: Vec, +r: F32, +col: U32, +al: F32, +cam: Cam, acc: Cells
) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +a = (i * k * 6.2831853 : F32)
      +b = ((i + 1.0) * k * 6.2831853 : F32)
      Fx.disc(m, (i + 1.0 : F32), k, c, r, col, al, cam,
        Fx.quad(c, Vec.add(c, Vec{(F32.cos(a) * r : F32), (F32.sin(a) * r : F32), 0.0}),
          Vec.add(c, Vec{(F32.cos(b) * r : F32), (F32.sin(b) * r : F32), 0.0}), c, col, 2,
          al, cam, acc))

# A point of a special's ribbon, local to the figure: kind 0 a loop
# about the chest wobbling in z, 2 a wake behind (the dash), 3 a helix
# rising from the feet; u of the way, at a phase and a radius.
def Fx.ribpt(+kind: U32, +u: F32, +phase: F32, +r: F32) -> Vec:
  +a = (u * 6.2831853 + phase : F32)
  +pulse = (F32.sin((u * 3.1415927 : F32)) * 0.52 : F32)
  +k2 = U32.is_eq(kind, 2)
  +k3 = U32.is_eq(kind, 3)
  Vec{Math.pick(k2, (0.0 - u * r : F32), Math.pick(k3, (F32.cos(a) * pulse : F32),
      (F32.cos(a) * r : F32))),
    Math.pick(k2, (0.9 + F32.sin((u * 9.4 + phase : F32)) * 0.09 : F32),
      Math.pick(k3, (0.1 + u * r : F32), (0.9 + F32.sin(a) * r * 0.66 : F32))),
    Math.pick(k2, (F32.sin(phase) * 0.22 : F32), Math.pick(k3, (F32.sin(a) * pulse : F32),
      (F32.sin((a * 2.0 + phase : F32)) * r * 0.24 : F32)))}

# n segments of a ribbon of a kind from segment i: a quad across the
# curve, its width swelling from 0.15 to 1 by sin(pi u).
def Fx.rib(
  n: Nat, +i: F32, +k: F32, +kind: U32, +phase: F32, +r: F32, +width: F32, +p: Vec,
  +face: F32, +col: U32, +al: F32, +cam: Cam, acc: Cells
) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +u = (i * k : F32)
      +a = Fx.ribpt(kind, u, phase, r)
      +b = Fx.ribpt(kind, (u + k : F32), phase, r)
      +nn = Vec.scale(Vec.unit(Vec.cross(Vec.sub(b, a), Vec{0.0, 0.0, 1.0})),
        (width * (0.15 + 0.85 * F32.sin((u * 3.1415927 : F32))) : F32))
      Fx.rib(m, (i + 1.0 : F32), k, kind, phase, r, width, p, face, col, al, cam,
        Fx.quad(Boss.at(p, face, Vec.add(a, nn)), Boss.at(p, face, Vec.add(b, nn)),
          Boss.at(p, face, Vec.sub(b, nn)), Boss.at(p, face, Vec.sub(a, nn)), col, 2, al,
          cam, acc))

# At most n segments of an arc of a sweep at a radius about p: fewer
# when it is small on the screen.
def Fx.segs(+n: F32, +sweep: F32, +r: F32, +p: Vec, +cam: Cam) -> F32:
  Math.min(n, F32.ceil((Grid.arc((r * Cam.px(cam, p) : F32)) * sweep * 0.159155 : F32)))

def Fx.nat(+n: F32) -> Nat:
  U32.to_nat(F32.to_u32(n))

# A thread: a thin ribbon of up to 20 segments and its soft halo.
def Fx.thread(
  +kind: U32, +phase: F32, +r: F32, +p: Vec, +face: F32, +col: U32, +al: F32, +cam: Cam,
  acc: Cells
) -> Cells:
  +n = Fx.segs(20.0, 6.2831853, r, p, cam)
  Fx.rib(Fx.nat(n), 0.0, (1.0 / n : F32), kind, phase, r, 0.018, p, face, col, al, cam,
    Fx.rib(Fx.nat(n), 0.0, (1.0 / n : F32), kind, phase, r, 0.055, p, face, col, (al * 0.12 : F32),
      cam, acc))

# The swing's arcs at the needle's angle: the cut (radius 2.9 heavy,
# 1.78 else), its halo and a thin inner line.
def Fx.cut(+heavy: Bool, +angle: F32, +col: U32, +p: Vec, +face: F32, +cam: Cam) -> Cells:
  +r = Math.pick(heavy, 2.9, 1.78)
  +n = Fx.segs(24.0, 1.9, r, p, cam)
  +m = Fx.segs(16.0, 1.75, r, p, cam)
  Fx.arc(Fx.nat(n), 0.0, (1.0 / n : F32), (angle - 0.90 : F32), 1.90, r,
    Math.pick(heavy, 0.30, 0.14), p, face, col, 0.75, cam,
    Fx.arc(Fx.nat(n), 0.0, (1.0 / n : F32), (angle - 1.06 : F32), 1.92, (r + 0.04 : F32),
      Math.pick(heavy, 0.60, 0.28), p, face, col, 0.12, cam,
      Fx.arc(Fx.nat(m), 0.0, (1.0 / m : F32), (angle - 1.18 : F32), 1.75, (r - 0.17 : F32),
        0.025, p, face, 16055017, 0.4, cam, CNil{})))

# The thorns from i of the down special's bloom: a horn from the feet
# out to a tip about the figure, a beam of light along it.
def Fx.thorn(
  n: Nat, +i: F32, +scale: F32, +p: Vec, +face: F32, +cam: Cam, acc: Cells
) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +a = (i * 0.785398 : F32)
      +root = {Vec{(F32.cos(a) * 0.34 : F32), 0.04, (F32.sin(a) * 0.30 : F32)} : Vec}
      +tip = {Vec{(F32.cos(a) * scale * 2.5 : F32), (scale * (0.9 + F32.abs(F32.sin(a))) : F32),
        (F32.sin(a) * scale * 1.5 : F32)} : Vec}
      Fx.thorn(m, (i + 1.0 : F32), scale, p, face, cam,
        Fx.beam(Boss.at(p, face, root), Boss.at(p, face, tip), 0.012, 0.004, 16568248, 0.7,
          cam, Cells.merge(acc, Hero.part(Inst.span(Horn{}, root, tip, (scale * 0.65 : F32),
            (scale * 0.6 : F32)), Mat.paint(13590649, 0.30, 0.15, 0.12), 6, 2, p, face, cam))))

# The special's light at u of its progress, scaled by sin(pi u): down,
# a bloom of eight thorns and a ring; else three threads (a wake for
# the dash, a helix rising for the upward ones, a loop else).
def Fx.special(down: Bool, +act: U32, +u: F32, +p: Vec, +face: F32, +cam: Cam) -> Cells:
  match down:
    case True{}:
      +scale = Math.max(0.02, F32.sin((u * 3.1415927 : F32)))
      Fx.thorn(8n, 0.0, scale, p, face, cam,
        Fx.thread(0, 0.0, (scale * 2.2 : F32), p, face, 15043735, 0.45, cam, CNil{}))
    case False{}:
      +scale = Math.max(0.02, F32.sin((u * 3.1415927 : F32)))
      +phase = (u * 15.0 : F32)
      +kind = Math.word(Act.up(act), 3, Math.word((U32.is_eq(act, 20) || U32.is_eq(act, 24)),
        2, 0))
      +r = Math.pick(U32.is_eq(kind, 2), 4.0, Math.pick(U32.is_eq(kind, 3), 3.7,
        (scale * 2.65 : F32)))
      Fx.thread(kind, phase, r, p, face, 15841738, (scale * 0.6 : F32), cam,
        Fx.thread(kind, (phase + 2.1 : F32), (r * 0.82 : F32), p, face, 15251616,
          (scale * 0.5 : F32), cam,
          Fx.thread(kind, (phase + 4.2 : F32), (r * 0.90 : F32), p, face, 9886675,
            (scale * 0.35 : F32), cam, CNil{})))

# The charge's glow (u of the full charge): a thread about the chest
# turning with time, an additive field before it and a ring, growing.
def Fx.charge(+u: F32, +t: F32, +p: Vec, +face: F32, +cam: Cam) -> Cells:
  +size = (0.25 + u * 0.20 : F32)
  +n = Fx.segs(24.0, 6.2831853, (0.24 + u * 0.22 : F32), p, cam)
  Fx.thread(0, (t * 0.10 : F32), (0.45 + u * 0.35 : F32), p, face, 16767096,
    (0.15 + u * 0.35 : F32), cam,
    Fx.arc(Fx.nat(n), 0.0, (1.0 / n : F32), 0.0, 6.2831853, (0.24 + u * 0.22 : F32), 0.022, p,
      face, 16768957, 0.65, cam,
      Mesh.of(Inst.ball(Globe{}, Boss.at(p, face, Vec{0.20, 1.08, 0.0}), size, size, size),
        Mat{16767404, 1.0, 0.0, 0.0, Plain{}, 2, (0.06 + u * 0.14 : F32)}, 8, 4, cam)))

# The guard's field: a translucent shell about the hero grown by the
# guard, pale in the parry window (its first 6 ticks), lit by a flash.
def Fx.guard(+guard: F32, +age: U32, +flash: U32, +p: Vec, +cam: Cam) -> Cells:
  +early = (age < 6 : U32)
  Mesh.of(Inst.ball(Globe{}, Vec.add(p, Vec{0.0, 0.86, 0.0}), (0.72 + guard * 0.003 : F32),
      (0.98 + guard * 0.003 : F32), 0.85),
    Mat.alpha(Math.word(early, 14482943, 5423871),
      (Math.pick(early, 0.14, 0.07) + Math.pick((flash > 0 : U32), 0.2, 0.0) : F32)), 12, 6,
    cam)

# The sparks from i of a hit: beams flying from the contact point.
def Fx.sparks(n: Nat, +i: F32, +p: Vec, +age: F32, +cam: Cam, acc: Cells) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +d = Vec.unit(Vec{F32.cos((i * 2.4 : F32)), F32.sin((i * 5.7 : F32)),
        F32.sin((i * 2.4 : F32))})
      Fx.sparks(m, (i + 1.0 : F32), p, age, cam,
        Fx.beam(Vec.add(p, Vec.scale(d, (age * 0.23 : F32))),
          Vec.add(p, Vec.scale(d, (age * 0.23 + 0.65 : F32))), 0.05, 0.02, 16769470, 1.0,
          cam, acc))

# The rays from i of a detonation at p of an age: every 22.5 degrees,
# flying out and thinning.
def Fx.rays(n: Nat, +i: F32, +p: Vec, +age: F32, +col: U32, +cam: Cam, acc: Cells) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +a = (i * 0.392699 : F32)
      +d = {Vec{F32.cos(a), F32.sin(a), 0.0} : Vec}
      +r = (0.2 + age * 0.12 : F32)
      Fx.rays(m, (i + 1.0 : F32), p, age, col, cam,
        Fx.beam(Vec.add(p, Vec.scale(d, r)),
          Vec.add(p, Vec.scale(d, (r + 1.5 - age * 0.02 : F32))),
          Math.max(0.0, (0.12 - age * 0.0025 : F32)), 0.02, col, 0.8, cam, acc))

# A detonation at p of an age: sixteen rays, a ring and a vertical
# beam, thinning over 42 ticks.
def Fx.boom(+p: Vec, +age: F32, +col: U32, +cam: Cam) -> Cells:
  Fx.rays(16n, 0.0, p, age, col, cam,
    Fx.arc(16n, 0.0, 0.0625, 0.0, 6.2831853, (0.4 + age * 0.13 : F32), 0.12,
      Vec.sub(p, Vec{0.0, 0.90, 0.34}), 0.0, col, 0.6, cam,
      Fx.beam(Vec.sub(p, Vec{0.0, 5.0, 0.0}), Vec.add(p, Vec{0.0, 5.0, 0.0}),
        Math.max(0.0, (0.20 - age * 0.012 : F32)), Math.max(0.0, (0.20 - age * 0.012 : F32)),
        16776677, 0.8, cam, CNil{})))

# The blade's trail: n quads back from the tip and the blade's middle
# at an age to the ones a tick earlier (the pose k ticks back), fading.
def Fx.trail(
  n: Nat, +k: U32, +p: Vec, +face: F32, +state: U32, +age: U32, +stun: U32, +tip: Vec,
  +mid: Vec, +cam: Cam, acc: Cells
) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +pose = Boss.pose(state, Math.word((age > k : U32), (age - k : U32), 0), stun)
      +t2 = Boss.tip(p, face, pose)
      +m2 = Boss.at(p, face, Vec.add(Pose.grip(pose), Vec.scale(Pose.dir(pose), 1.5)))
      Fx.trail(m, (k + 1 : U32), p, face, state, age, stun, t2, m2, cam,
        Fx.quad(tip, t2, m2, mid, 10352639, 2, (0.5 - U32.to_f32(k) * 0.08 : F32), cam, acc))

# The slam's shockwave: a band of quads from i about (x, y) on the
# floor (an ellipse, as the arena), of a radius and a height.
def Fx.shock(
  n: Nat, +i: F32, +x: F32, +y: F32, +r: F32, +h: F32, +al: F32, +cam: Cam, acc: Cells
) -> Cells:
  match n:
    case 0n:
      acc
    case 1n+m:
      +a = (i * 0.2617994 : F32)
      +b = (a + 0.2617994 : F32)
      +ax = (x + F32.cos(a) * r : F32)
      +az = (F32.sin(a) * r * 0.48 : F32)
      +bx = (x + F32.cos(b) * r : F32)
      +bz = (F32.sin(b) * r * 0.48 : F32)
      Fx.shock(m, (i + 1.0 : F32), x, y, r, h, al, cam,
        Fx.quad(Vec{ax, y, az}, Vec{bx, y, bz}, Vec{bx, (y + h : F32), bz},
          Vec{ax, (y + h : F32), az}, 11197695, 2, al, cam, acc))

def Fx.one(+f: Fx, +cam: Cam) -> Cells:
  match f:
    case Swing{p, face, angle, charge}:
      +heavy = (charge > 2 : U32)
      Fx.cut(heavy, angle, Math.word(heavy, 16768423, 14154209), p, face, cam)
    case Special{p, face, act, u}:
      Fx.special(Act.down(act), act, u, p, face, cam)
    case Charge{p, face, u, t}:
      Fx.charge(u, t, p, face, cam)
    case Dodge{p, face, age}:
      Fx.thread(0, (U32.to_f32(age) * 0.15 : F32), 0.75, p, face, 8381419,
        (U32.to_f32(age) / 70.0 : F32), cam, CNil{})
    case Guard{p, guard, age, flash}:
      Fx.guard(guard, age, flash, p, cam)
    case Spark{p, age}:
      Fx.sparks(16n, 0.0, p, U32.to_f32(age), cam, CNil{})
    case Boom{x, y, age, who}:
      Fx.boom(Vec{x, y, 1.0}, age, Math.word(U32.is_eq(who, 1), 16285568, 16249550), cam)
    case Slash{p, face, state, age, stun}:
      +k = Boss.pose(state, age, stun)
      Fx.trail(6n, 1, p, face, state, age, stun, Boss.tip(p, face, k),
        Boss.at(p, face, Vec.add(Pose.grip(k), Vec.scale(Pose.dir(k), 1.5))), cam, CNil{})
    case Shock{x, y, age}:
      +fade = (1.0 - U32.to_f32(age) / 20.0 : F32)
      Fx.shock(24n, 0.0, x, y, (0.6 + U32.to_f32(age) * 0.30 : F32), (0.4 * fade : F32),
        (0.55 * fade : F32), cam, CNil{})
    case Parry{p, age}:
      Fx.disc(12n, 0.0, 0.0833333, p, (0.9 - U32.to_f32(age) * 0.07 : F32), 14482943,
        (0.7 - U32.to_f32(age) * 0.08 : F32), cam, CNil{})
    case Aura{p, t}:
      +al = (0.06 + 0.02 * F32.sin((t * 0.25 : F32)) : F32)
      +c = Vec.add(p, Vec{0.0, 0.0, 0.3})
      Fx.disc(12n, 0.0, 0.0833333, c, 1.0, 16726560, al, cam,
        Fx.disc(12n, 0.0, 0.0833333, c, 0.55, 16726560, (al * 1.5 : F32), cam, CNil{}))

def Fx.add(on: Bool, fx: Fx, rest: List<&2, Fx>) -> List<&2, Fx>:
  match on:
    case False{}:
      rest
    case True{}:
      fx <> rest

# The boss's effects: its blade's trail while live and 4 ticks after,
# the slam's wave, the block's flash at the hilt, the aura when enraged.
def Fx.boss(+b: Boss, +t: F32, rest: List<&2, Fx>) -> List<&2, Fx>:
  Boss{p, _, face, hp, stun, _, state, age, _, _, _} = b
  Vec{x, y, _} = p
  +k = Boss.pose(state, age, stun)
  +wind = Boss.wind(state)
  Fx.add(((state > 0 : U32) && U32.is_eq(stun, 0) && (age >= wind : U32)
      && (age < (wind + Boss.act(state) + 4 : U32) : U32)), Slash{p, face, state, age, stun},
    Fx.add((U32.is_eq(state, 7) && (age < 20 : U32)), Shock{x, y, age},
      Fx.add((U32.is_eq(state, 6) && (age < 8 : U32)), Parry{Boss.hilt(p, face, k), age},
        Fx.add(((hp < 160.0 : F32) && (hp > 0.0 : F32)),
          Aura{Boss.at(p, face, Pose.spine(k, 1.0)), t}, rest))))

# The detonation while it lasts, held inside the lens.
def Fx.blast(m: Maybe<&2, Blast>, +l: Lens, +t: F32, rest: List<&2, Fx>) -> List<&2, Fx>:
  match m:
    case None{}:
      rest
    case Some{b}:
      Blast{x, y, born, who} = b
      Lens{cx, cy, w, _, _, _} = l
      +age = (t - U32.to_f32(born) : F32)
      Fx.add((age < 42.0 : F32),
        Boom{Math.clamp(x, (cx - w * 0.44 : F32), (cx + w * 0.44 : F32)),
          Math.clamp(y, (cy - w * 0.22 : F32), (cy + w * 0.22 : F32)), Math.max(0.0, age), who},
        rest)

def Fx.list(+g: Game, +t: F32) -> List<&2, Fx>:
  Game{_, _, _, _, hero, boss, flash, _, _, lens, blast} = g
  Fighter{p, _, face, _, guard, _, action, age, _, _, _, _, charge} = hero
  +hit = Act.hit(action)
  +len = U32.to_f32(Act.length(action))
  +attack = Act.attack(action)
  +special = Act.special(action)
  Fx.add((attack && Bool.not(special) && (age <= (hit + 3 : U32) : U32)
      && ((age + 4 : U32) >= hit : U32)), Swing{p, face, Hero.angle(action, age), charge},
    Fx.add((attack && special),
      Special{p, face, action, Math.sat(((len - U32.to_f32(age)) / len : F32))},
      Fx.add(Act.charging(action), Charge{p, face, Math.sat((U32.to_f32(charge) / 45.0 : F32)), t},
        Fx.add(U32.is_eq(action, 6), Dodge{p, face, age},
          Fx.add(U32.is_eq(action, 3), Guard{p, guard, age, flash},
            Fx.add((flash > 0 : U32), Spark{Game.contact(hero, boss), (7 - flash : U32)},
              Fx.blast(blast, lens, t, Fx.boss(boss, t, []))))))))

def Fx.draw(fx: List<&2, Fx>, +cam: Cam) -> Cells:
  match fx:
    case Nil{}:
      CNil{}
    case Con{f, rest}:
      Cells.merge(Fx.one(f, cam), Fx.draw(rest, cam))

# Text
# ----

# A stroke font: a glyph is a string whose first character is its
# advance in half units (code - 48) and whose rest are the points of
# its strokes (code - 48 = x + 5 y over a 5 x 8 grid, y down from the
# cap line, 6 the baseline), a space lifting the pen. Capitals, digits
# and the marks % / + . , ' -; a lowercase letter is its capital at
# 0.72, a small capital. Made by .tmp/sb/t12/font.py.
def Font.glyph(c: U32) -> String:
  match c:
    case 65:
      ";N2R EG"
    case 66:
      ";N039>B? BHMQN"
    case 67:
      ";9315IOQM"
    case 68:
      ";N039MQN"
    case 69:
      ":40NR ?B"
    case 70:
      ":40N ?B"
    case 71:
      ";9315IOQMCA"
    case 72:
      ";0N ?C 4R"
    case 73:
      "50N"
    case 74:
      ":4MQOI"
    case 75:
      ";0N 4D @R"
    case 76:
      ":0NR"
    case 77:
      ";N0A4R"
    case 78:
      ";N0R4"
    case 79:
      ";139MQOI51"
    case 80:
      ";N039>B?"
    case 81:
      ";139MQOI51 FW"
    case 82:
      ";N039>B? AR"
    case 83:
      ";9315:@BHMQOI"
    case 84:
      ":04 2P"
    case 85:
      ";0IOQM4"
    case 86:
      ";0P4"
    case 87:
      "<0O<Q4"
    case 88:
      ";0R 4N"
    case 89:
      ";0A4 AP"
    case 90:
      ";04NR"
    case 48:
      ";139MQOI51"
    case 49:
      "8:2P"
    case 50:
      ";5139>NR"
    case 51:
      ";5139>B@ BHMQOI"
    case 52:
      ";Q3DH"
    case 53:
      ";40?BHMQOI"
    case 54:
      ";9315IOQMHB?"
    case 55:
      ":04O"
    case 56:
      ";@:5139>B@DIOQMHB"
    case 57:
      ";IOQM9315:@C"
    case 37:
      "<02<:0 4N FHRPF"
    case 47:
      "94N"
    case 43:
      ";7K ?C"
    case 46:
      "4IN"
    case 44:
      "4JOS"
    case 39:
      "40:"
    case 45:
      "8?B"
    case 32:
      "6"
    case _:
      "6"

# A stroke from (ax, ay) to (bx, by) in pixels: a quad half wv wide
# across an upright, wh across a bar (the serif face's contrast), its
# ends as far past the points so that joints close (slab ends were
# tried: they stud every round glyph), wound for the opaque path and
# nearer than anything (inverse depth 3000).
def Text.seg(
  +ax: F32, +ay: F32, +bx: F32, +by: F32, +wv: F32, +wh: F32, +col: U32, cells: Cells
) -> Cells:
  +dx = (bx - ax : F32)
  +dy = (by - ay : F32)
  +l = F32.sqrt((dx * dx + dy * dy : F32))
  +h = (wh + (wv - wh) * F32.abs(dy) / l : F32)
  +ex = (dx / l * h : F32)
  +ey = (dy / l * h : F32)
  Quad.put((ax - ex - ey : F32), (ay - ey + ex : F32), (bx + ex - ey : F32),
    (by + ey + ex : F32), (bx + ex + ey : F32), (by + ey - ex : F32), (ax - ex + ey : F32),
    (ay - ey - ex : F32), 3000.0, col, 0, 1.0, cells)

def Text.stroke(
  on: Bool, +ax: F32, +ay: F32, +bx: F32, +by: F32, +wv: F32, +wh: F32, +col: U32,
  cells: Cells
) -> Cells:
  match on:
    case False{}:
      cells
    case True{}:
      Text.seg(ax, ay, bx, by, wv, wh, col, cells)

# The strokes of a glyph's points from x on the baseline, u a grid
# step: a point after another (the pen down at (px, py)) is a stroke
# from it; a space lifts the pen.
def Text.strokes(
  g: String, down: Bool, +px: F32, +py: F32, +x: F32, +base: F32, +u: F32, +wv: F32,
  +wh: F32, +col: U32, cells: Cells
) -> Cells:
  match g:
    case SNil{}:
      cells
    case SCon{Chr{+c}, rest}:
      +k = (c - 48 : U32)
      +on = (c > 32 : U32)
      +qx = (x + U32.to_f32((k % 5 : U32)) * u : F32)
      +qy = (base - (6.0 - U32.to_f32((k / 5 : U32))) * u : F32)
      Text.strokes(rest, on, qx, qy, x, base, u, wv, wh, col,
        Text.stroke(Bool.and(down, on), px, py, qx, qy, wv, wh, col, cells))

def Text.adv(g: String) -> F32:
  match g:
    case SNil{}:
      0.0
    case SCon{Chr{a}, pts}:
      U32.to_f32((a - 48 : U32))

def Text.pts(g: String) -> String:
  match g:
    case SNil{}:
      SNil{}
    case SCon{_, pts}:
      pts

# Text from x on the baseline (pixels), u a grid step of a capital.
def Text.go(
  s: String, +x: F32, +base: F32, +u: F32, +wv: F32, +wh: F32, +col: U32, cells: Cells
) -> Cells:
  match s:
    case SNil{}:
      cells
    case SCon{Chr{+c}, rest}:
      +low = ((c >= 97) && (c <= 122) : U32)
      +k = (u * Math.pick(low, 0.72, 1.0) : F32)
      +code = Math.word(low, (c - 32 : U32), c)
      Text.go(rest, (x + Text.adv(Font.glyph(code)) * k * 0.5 : F32), base, u, wv, wh, col,
        Text.strokes(Text.pts(Font.glyph(code)), False{}, 0.0, 0.0, x, base, k, wv, wh, col,
          cells))

# Text of a size and style (0 sans, 1 serif: thick uprights and thin
# bars, 2 bold) at (x, y), the top left of its box on the original's
# 1024 x 640 canvas (the drawable is 1.875 of it): the baseline sits
# 0.88 of the size down, the capitals rise 0.7 of it.
def Text.put(
  +x: F32, +y: F32, +size: F32, +style: U32, +col: U32, s: String, cells: Cells
) -> Cells:
  +sz = (size * 1.875 : F32)
  +w = Math.max(0.8, (sz * Math.pick(U32.is_eq(style, 2), 0.06,
    Math.pick(U32.is_eq(style, 1), 0.05, 0.035)) : F32))
  Text.go(s, (x * 1.875 : F32), (y * 1.875 + sz * 0.88 : F32), (sz * 0.116667 : F32), w,
    Math.pick(U32.is_eq(style, 1), Math.max(0.8, (w * 0.5 : F32)), w), col, cells)

# HUD
# ---

# The original's HUD (hud_native.bend) on its 1024 x 640 canvas. A
# rectangle of it: alpha over the scene (m 1), or opaque (m 0) at the
# inverse depth d (the nearer opaque wins a pixel, so the text at
# 3000 stands over the bars at 2500 and 2000 and the panels at 1000,
# in any order).
def Hud.rect(
  +x: F32, +y: F32, +w: F32, +h: F32, +col: U32, +m: U32, +al: F32, +d: F32, cells: Cells
) -> Cells:
  +x0 = (x * 1.875 : F32)
  +y0 = (y * 1.875 : F32)
  +x1 = ((x + w) * 1.875 : F32)
  +y1 = ((y + h) * 1.875 : F32)
  Quad.put(x0, y0, x0, y1, x1, y1, x1, y0, d, col, m, al, cells)

def Move.name(act: U32) -> String:
  match act:
    case 2:
      "Silk snare"
    case 3:
      "Guard"
    case 6:
      "Air dodge"
    case 7:
      "Crouch"
    case 20:
      "Needle dash"
    case 21:
      "Loom ascent"
    case 22:
      "Thorn bloom"
    case 23:
      "Silk cyclone"
    case 24:
      "Needle dive"
    case 25:
      "Loom ascent"
    case 26:
      "Crimson fall"
    case 30:
      "Charging side smash"
    case 31:
      "Charging sky smash"
    case 32:
      "Charging low smash"
    case _:
      "J  Needle     K  Silk"

def Hud.parry(on: Bool, cells: Cells) -> Cells:
  match on:
    case False{}:
      cells
    case True{}:
      Text.put(472.0, 91.0, 20.0, 1, 14938614, "PARRY", cells)

# The fight's panel: the hero's damage, lives and guard, the move's
# name and the smash charge, the boss's strain and vitality, the keys,
# and PARRY over the stage on one.
def Hud.fight(+g: Game, cells: Cells) -> Cells:
  Game{_, _, _, _, hero, boss, flash, _, _, _, _} = g
  Fighter{_, _, _, damage, guard, _, action, _, _, stocks, _, _, charge} = hero
  Boss{_, _, _, hp, stun, strain, _, _, _, _, _} = boss
  Hud.rect(0.0, 549.0, 1024.0, 91.0, 592914, 1, 0.82, 1000.0,
    Hud.rect(36.0, 549.0, 952.0, 0.6, 3753540, 0, 1.0, 2000.0,
      Text.put(37.0, 557.0, 11.0, 2, 15120588, "THE NEEDLE",
        Text.put(34.0, 571.0, 42.0, 1, Math.word((damage > 80.0 : F32), 15572866, 15920620),
          U32.show(F32.to_u32(damage)) ++ "%",
          Text.put(155.0, 578.0, 16.0, 1, 12434368, U32.show(stocks) ++ " lives",
            Hud.rect(155.0, 610.0, 110.0, 2.0, 2832972, 0, 1.0, 2000.0,
              Hud.rect(155.0, 610.0, (110.0 * guard / 100.0 : F32), 2.0, 7977935, 0, 1.0, 2500.0,
                Text.put(669.0, 557.0, 11.0, 2, 14405571, Boss.name(),
                  Text.put(898.0, 571.0, 42.0, 1, 14788253, U32.show(F32.to_u32(strain)) ++ "%",
                    Hud.rect(670.0, 610.0, 192.0, 3.0, 2832972, 0, 1.0, 2000.0,
                      Hud.rect(670.0, 610.0, (192.0 * hp / 360.0 : F32), 3.0,
                        Math.word((hp < 160.0 : F32), 14524034, 13482665), 0, 1.0, 2500.0,
                        Text.put(670.0, 584.0, 10.0, 0, 9084575, "VITALITY",
                          Text.put(375.0, 580.0, 14.0, 1, 13030592, Move.name(action),
                            Hud.rect(377.0, 606.0, Math.pick(Act.charging(action),
                              (140.0 * Math.sat((U32.to_f32(charge) / 45.0 : F32)) : F32), 0.0),
                              2.0, 15644068, 0, 1.0, 2500.0,
                              Text.put(360.0, 623.0, 9.0, 0, 9084575,
                                "I  Jump    L  Guard / dodge    P  Pause",
                                Hud.parry(((flash > 0 : U32) && U32.is_eq(action, 3)
                                  && (stun > 0 : U32)), cells))))))))))))))))

# The title: the name, a rule and the tagline, the button and the help.
def Hud.title(cells: Cells) -> Cells:
  Text.put(41.0, 115.0, 75.0, 1, 15920360, "Moon",
    Text.put(41.0, 181.0, 75.0, 1, 15920360, "Sever",
      Hud.rect(48.0, 270.0, 43.0, 1.0, 12694169, 1, 0.8, 1000.0,
        Text.put(47.0, 286.0, 16.0, 1, 12107707, "One needle. One severing blade.",
          Hud.rect(375.0, 503.0, 274.0, 39.0, 987680, 1, 0.83, 1000.0,
            Hud.rect(375.0, 503.0, 274.0, 1.0, 8155507, 0, 1.0, 2000.0,
              Text.put(395.0, 511.0, 18.0, 2, 15064013, "L",
                Text.put(449.0, 510.0, 19.0, 1, 15330267, "Begin the duel",
                  Text.put(295.0, 558.0, 11.5, 0, 11647924,
                    "Move + J / K changes your attack. Hold a direction + J to charge a smash.",
                    Text.put(390.0, 585.0, 11.5, 0, 9544869,
                      "I  Jump     L  Guard / air dodge     P  Pause", cells))))))))))

# The end of a duel: its title at x, its line at x2, the choices.
def Hud.end(+x: F32, +col: U32, title: String, +x2: F32, line: String, cells: Cells) -> Cells:
  Text.put(x, 113.0, 43.0, 1, col, title, Text.put(x2, 169.0, 17.0, 1, 11715764, line,
    Text.put(414.0, 495.0, 15.0, 0, 14540496, "L  Duel again     K  Back", cells)))

def Hud.pause(cells: Cells) -> Cells:
  Hud.rect(343.0, 171.0, 340.0, 142.0, 724246, 1, 0.94, 1000.0,
    Text.put(447.0, 191.0, 40.0, 1, 15263695, "Paused",
      Text.put(410.0, 265.0, 15.0, 0, 11715764, "L  Continue     K  Back", cells)))

# The screen of a mode: the title alone; the fight's panel under the
# win, the loss or the pause.
def Hud.screen(title: Bool, won: Bool, lost: Bool, paused: Bool, +g: Game, cells: Cells) -> Cells:
  match title won lost paused:
    case True{} _ _ _:
      Hud.title(cells)
    case False{} True{} _ _:
      Hud.end(327.0, 15135440, "Thread unbroken", 369.0, "The blade falls silent. One final cut.",
        Hud.fight(g, cells))
    case False{} False{} True{} _:
      Hud.end(373.0, 15049618, "Silk undone", 391.0, "Rise again. Learn its rhythm.",
        Hud.fight(g, cells))
    case False{} False{} False{} True{}:
      Hud.pause(Hud.fight(g, cells))
    case False{} False{} False{} False{}:
      Hud.fight(g, cells)

# The HUD of a game: the name and the boss's, then its mode's screen.
def Hud.build(+g: Game, cells: Cells) -> Cells:
  Game{_, _, _, mode, hero, boss, _, _, _, _, _} = g
  Text.put(34.0, 22.0, 20.0, 1, 14801615, "MOON SEVER",
    Text.put(35.0, 46.0, 8.5, 2, 9019827, Boss.name(),
      Hud.screen(U32.is_eq(mode, 0), U32.is_eq(mode, 2), U32.is_eq(mode, 3), U32.is_eq(mode, 4),
        g, cells)))

# A cell's list freed, one flat loop; nothing (CNil) comes back, a
# merge's identity.
def Tris.free(ts: Tris) -> Cells:
  match ts:
    case TNil{}:
      CNil{}
    case TCons{_, n}:
      Tris.free(n)

# A subtree freed: a match frees a node, the loop a cell's list.
def Cells.free(c: Cells) -> Cells:
  match c:
    case CNil{}:
      CNil{}
    case CLeaf{_, ts}:
      Tris.free(ts)
    case CQua{a, b, cc, d}:
      Cells.m4(Cells.free(a), Cells.free(b), Cells.free(cc), Cells.free(d))

# The last scene consumed on the host after the device read it: a
# parallel walk of k levels, then the free.
def Cells.drop(+k: Nat, c: Cells) -> Cells:
  match k c:
    case 1n+e CQua{tl, tr, bl, br}:
      a b cc d = Cells.drop(e, tl) Cells.drop(e, tr) Cells.drop(e, bl) Cells.drop(e, br)
      Cells.m4(a, b, cc, d)
    case _ _:
      Cells.free(c)

# The scene of a game state at the view's clock: the hero and his cape,
# the boss, the stage in five branches (each grows in its own row of
# the host's rings), the effects, the HUD; the last scene dropped
# beside them.
def Scene.build(+g: Game, +t: F32, used: Cells) -> Cells:
  Game{_, _, _, _, hero, boss, flash, cloth, garb, lens, _} = g
  +cam = Cam.at(lens, t, flash, Game.contact(hero, boss))
  a b c d1 d2 d3 d4 d5 h e u = Hero.build(hero, t, cam) Cape.of(cloth, cam)
    Boss.build(boss, garb, t, cam) Stage.top(cam) Stage.deep(cam)
    Stage.arch((0.0 - 9.5 : F32), cam) Stage.pair(cam) Stage.rest(cam) Hud.build(g, CNil{})
    Fx.draw(Fx.list(g, t), cam) Cells.drop(4n, used)
  Cells.merge(Cells.m4(a, b, c, Cells.merge(Cells.merge(Cells.merge(d1, d2), d3), Cells.merge(d4,
    d5))), Cells.merge(e, Cells.merge(h, u)))

# Sky
# ---

# The sky at a place: the ridge heights (the lower, 2, in front of 1)
# of a column, the star (centre and size, size 0 for none, its colour)
# of its square and its band.
type Sky is Data:
  Sky{r2: F32, r1: F32, sx: F32, sy: F32, ss: F32, sc: U32, band: U32}

# A mountain ridge (layer 1 or 2) as a screen height over the column
# xf: the original's over 1024 x 640, scaled by 1.875.
def Sky.ridge(+l: F32, +xf: F32) -> F32:
  +f = (xf / 120.0 : F32)
  (497.0 + 165.0 * l - 79.0 * F32.sin((0.7 * f + 2.0 * l : F32))
    - 52.0 * F32.sin((1.9 * f + 4.0 * l : F32)) - 30.0 * F32.cos((3.7 * f : F32)) : F32)

# The gradient in bands of 16 rows: (16, 26, 36) to (49, 61, 72).
def Sky.band(+y: U32) -> U32:
  +u = (U32.to_f32((y >> 4n : U32)) / 75.0 : F32)
  Math.pack((0.063 + 0.129 * u : F32), (0.102 + 0.137 * u : F32),
    (0.141 + 0.141 * u : F32))

# The star of the original's 16 (a diamond of half width 1.3 or 0.65,
# two greys) whose diamond meets the h-square at (x, y), walked from i.
def Sky.star(n: Nat, +i: F32, +x: F32, +y: F32, +h: F32, +sky: Sky) -> Sky:
  match n:
    case 0n:
      sky
    case 1n+k:
      Sky{r2, r1, sx, sy, ss, sc, band} = sky
      +px = (((i * 137.508 + 31.0) % 1024.0 : F32) * 1.875 : F32)
      +py = ((12.0 + F32.abs(F32.sin((i * 4.73 : F32))) * 228.0) * 1.875 : F32)
      +ii = F32.to_u32(i)
      +s = (Math.pick(U32.is_eq((ii .&. 3 : U32), 0), 1.3, 0.65) * 1.875 : F32)
      +hit = ((px + s > x) && (px - s < x + h) && (py + s * 2.0 > y)
        && (py - s * 2.0 < y + h) : F32)
      Sky.star(k, (i + 1.0 : F32), x, y, h, Sky{r2, r1, Math.pick(hit, px, sx),
        Math.pick(hit, py, sy), Math.pick(hit, s, ss),
        Math.word(hit, Math.word(U32.is_eq((ii .&. 1 : U32), 0), 10989229, 6253955), sc),
        band})

def Sky.stars(low: Bool, +x: F32, +y: F32, +h: F32, +sky: Sky) -> Sky:
  match low:
    case True{}:
      sky
    case False{}:
      Sky.star(16n, 0.0, x, y, h, sky)

# The sky of the h-square at (x, y): its ridges at its centre column,
# its star (none below the stars' reach) and its band.
def Sky.of(+x: U32, +y: U32, +h: U32) -> Sky:
  +xc = (U32.to_f32(x) + 0.5 * U32.to_f32(h) : F32)
  Sky.stars((y > 460 : U32), U32.to_f32(x), U32.to_f32(y), U32.to_f32(h),
    Sky{Sky.ridge(2.0, xc), Sky.ridge(1.0, xc), 0.0, 0.0, 0.0, 0, Sky.band(y)})

# Does a ridge or the star cross the h-square at (x, y)? A ridge's slope
# is under 1.6, so it moves under h across the square.
def Sky.mixed(+sky: Sky, +x: U32, +y: U32, +h: U32) -> Bool:
  Sky{r2, r1, sx, sy, ss, _, band} = sky
  +xf = U32.to_f32(x)
  +yf = U32.to_f32(y)
  +hf = U32.to_f32(h)
  (((yf < r2 + hf + 1.0) && (yf + hf > r2 - hf - 1.0))
    || ((yf < r1 + hf + 1.0) && (yf + hf > r1 - hf - 1.0))
    || ((ss > 0.0) && (sx + ss > xf) && (sx - ss < xf + hf) && (sy + ss * 2.0 > yf)
      && (sy - ss * 2.0 < yf + hf)) : F32)

# The colour under the ridges (layer 2 in front), a star or the band.
def Sky.layer(m2: Bool, m1: Bool, star: Bool, +sc: U32, +band: U32) -> U32:
  match m2 m1 star:
    case True{} _ _:
      2042676
    case False{} True{} _:
      2437689
    case False{} False{} True{}:
      sc
    case False{} False{} False{}:
      band

def Sky.at(+x: U32, +y: U32, +sky: Sky) -> U32:
  Sky{r2, r1, sx, sy, ss, sc, band} = sky
  +xf = (U32.to_f32(x) + 0.5 : F32)
  +yf = (U32.to_f32(y) + 0.5 : F32)
  Sky.layer((yf > r2 : F32), (yf > r1 : F32),
    ((ss > 0.0) && ((F32.abs((xf - sx : F32)) * 2.0 + F32.abs((yf - sy : F32)) : F32)
      <= (ss * 2.0 : F32)) : F32), sc, band)

# The sky of the columns x, x + 1 when the tile needs pixels, else the
# tile's.
def Sky.col(per: Bool, +x: U32, +sky: Sky) -> Sky:
  match per:
    case False{}:
      sky
    case True{}:
      Sky{_, _, sx, sy, ss, sc, band} = sky
      +xc = (U32.to_f32(x) + 1.0 : F32)
      Sky{Sky.ridge(2.0, xc), Sky.ridge(1.0, xc), sx, sy, ss, sc, band}

# Frame
# -----

# The nearest opaque hit at a pixel: its inverse depth, its colour and
# the index of its triangle in the tile's list (0: none).
type Hit is Data:
  Hit{w: F32, c: U32, i: U32}

# The hits of a 2 x 2 block, and did a pixel take a blend.
type Blk is Data:
  Blk{+h0: Hit, +h1: Hit, +h2: Hit, +h3: Hit, mixed: Bool}

# The four quadrants of the last frame's image of a region.
type Four is Data:
  Four{a: Image, b: Image, c: Image, d: Image}

# The filter's answer: the count, the opaque list and the transparent
# list.
type Filt is Data:
  Filt{+n: U32, ts: Tris, bs: Tris}

def Tris.put(on: Bool, +t: Tri, acc: Tris) -> Tris:
  match on:
    case True{}:
      TCons{t, acc}
    case False{}:
      acc

# A triangle whose box meets the tile's: kept when no edge separates the
# tile's corner pixels from it.
def Tris.test(
  over: Bool, +t: Tri, +fx0: F32, +fy0: F32, +fx1: F32, +fy1: F32, f: Filt
) -> Filt:
  match over:
    case False{}:
      f
    case True{}:
      Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
        m, al, bx0, by0, bx1, by1} = t
      Filt{n, acc, bcc} = f
      +hit = Tri.cover(1.0, t, fx0, fy0, fx1, fy1)
      +opaque = U32.is_eq(m, 0)
      Filt{(n + Math.word(hit, 1, 0) : U32), Tris.put(Bool.and(hit, opaque), t, acc),
        Tris.put(Bool.and(hit, Bool.not(opaque)), t, bcc)}

# The triangles of the borrowed list that meet the pixel centres of
# [x0, x1] x [y0, y1], onto the filter's lists.
def Tris.filter(cs: Tris, +x0: U32, +y0: U32, +x1: U32, +y1: U32, f: Filt) -> Filt:
  match cs:
    case TNil{}:
      f
    case TCons{t, m}:
      Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
        md, al, bx0, by0, bx1, by1} = t
      Tris.filter(m, x0, y0, x1, y1, Tris.test(
        ((bx0 <= x1) && (bx1 >= x0) && (by0 <= y1) && (by1 >= y0) : U32), t,
        (U32.to_f32(x0) + 0.5 : F32), (U32.to_f32(y0) + 0.5 : F32),
        (U32.to_f32(x1) + 0.5 : F32), (U32.to_f32(y1) + 0.5 : F32), f))

# Is the point in the triangle? A hair of slack closes the cracks along
# the edges where a patch meets two finer ones.
def Tri.in(+l0: F32, +l1: F32) -> Bool:
  ((l0 >= 0.0) && (l1 >= 0.0) && (l0 + l1 <= 1.004) : F32)

# The hit when the triangle i is nearer at the point, shaded there.
def Blk.hit(
  hit: Bool, +t: Tri, +w: F32, +i: U32, +px: F32, +py: F32, +old: Hit
) -> Hit:
  match hit:
    case False{}:
      old
    case True{}:
      Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
        m, al, x0, y0, x1, y1} = t
      Hit{w, Math.pack((rc + ru * px + rv * py : F32), (gc + gu * px + gv * py : F32),
        (bc + bu * px + bv * py : F32)), i}

def Blk.at(none: Bool, +c: U32, +x: U32, +y: U32, +sky: Sky) -> U32:
  match none:
    case False{}:
      c
    case True{}:
      Sky.at(x, y, sky)

# A colour blended over the old one: a lerp by al (alpha), or al of it
# added.
def Blend.mix(
  lerp: Bool, +al: F32, +r: F32, +g: F32, +b: F32, +oldr: F32, +oldg: F32,
  +oldb: F32
) -> U32:
  match lerp:
    case True{}:
      Math.pack((oldr + (r - oldr) * al : F32), (oldg + (g - oldg) * al : F32),
        (oldb + (b - oldb) * al : F32))
    case False{}:
      Math.pack((oldr + r * al : F32), (oldg + g * al : F32), (oldb + b * al : F32))

# A colour over the old one by the triangle's mode: a soft one lerps
# the shadow's tint by its alpha under cos^2 of the distance from its
# centre (the r and g planes over w: perspective-correct).
def Blend.mode(
  soft: Bool, +m: U32, +al: F32, +r: F32, +g: F32, +b: F32, +w: F32, +old: U32
) -> U32:
  match soft:
    case False{}:
      Blend.mix(U32.is_eq(m, 1), al, r, g, b, Math.chan(old, 16n), Math.chan(old, 8n),
        Math.chan(old, 0n))
    case True{}:
      +c = F32.cos((1.5707963 * Math.min(1.0, (F32.sqrt((r * r + g * g : F32)) / w : F32)) : F32))
      Blend.mix(True{}, (al * c * c : F32), Math.chan(527380, 16n), Math.chan(527380, 8n),
        Math.chan(527380, 0n), Math.chan(old, 16n), Math.chan(old, 8n), Math.chan(old, 0n))

def Blend.px(hit: Bool, +t: Tri, +px: F32, +py: F32, +old: U32) -> U32:
  match hit:
    case False{}:
      old
    case True{}:
      Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
        m, al, x0, y0, x1, y1} = t
      Blend.mode(U32.is_eq(m, 3), m, al, (rc + ru * px + rv * py : F32),
        (gc + gu * px + gv * py : F32), (bc + bu * px + bv * py : F32),
        (wc + wu * px + wv * py : F32), old)

def Blk.one(same: Bool, +k0: U32, +k1: U32, +k2: U32, +k3: U32) -> Image:
  match same:
    case True{}:
      Pix{k0}
    case False{}:
      Qua{Pix{k0}, Pix{k1}, Pix{k2}, Pix{k3}}

# The block's image: one Pix under one opaque triangle nothing blended
# over, or of one colour; else its four pixels.
def Blk.four(+b: Blk) -> Image:
  Blk{h0, h1, h2, h3, mixed} = b
  Hit{_, k0, i0} = h0
  Hit{_, k1, i1} = h1
  Hit{_, k2, i2} = h2
  Hit{_, k3, i3} = h3
  Blk.one((U32.is_eq(i0, i1) && U32.is_eq(i1, i2) && U32.is_eq(i2, i3)
    && (((i0 > 0) && Bool.not(mixed))
      || (U32.is_eq(k0, k1) && U32.is_eq(k1, k2) && U32.is_eq(k2, k3))) : U32),
    k0, k1, k2, k3)

# A transparent triangle nearer than the block's opaque hits blended
# over its colours; mixed when a pixel took it.
def Blend.step(+t: Tri, +px: F32, +py: F32, +b: Blk) -> Blk:
  Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
    m, al, bx0, by0, bx1, by1} = t
  Blk{h0, h1, h2, h3, mixed} = b
  Hit{w0, k0, i0} = h0
  Hit{w1, k1, i1} = h1
  Hit{w2, k2, i2} = h2
  Hit{w3, k3, i3} = h3
  +l0 = (a0 * px + b0 * py + c0 + 0.002 : F32)
  +l1 = (a1 * px + b1 * py + c1 + 0.002 : F32)
  +w = (wc + wu * px + wv * py : F32)
  +px1 = (px + 1.0 : F32)
  +py1 = (py + 1.0 : F32)
  +q0 = Bool.and(Tri.in(l0, l1), (w > w0 : F32))
  +q1 = Bool.and(Tri.in((l0 + a0 : F32), (l1 + a1 : F32)), (w + wu > w1 : F32))
  +q2 = Bool.and(Tri.in((l0 + b0 : F32), (l1 + b1 : F32)), (w + wv > w2 : F32))
  +q3 = Bool.and(Tri.in((l0 + a0 + b0 : F32), (l1 + a1 + b1 : F32)),
    (w + wu + wv > w3 : F32))
  Blk{Hit{w0, Blend.px(q0, t, px, py, k0), i0}, Hit{w1, Blend.px(q1, t, px1, py, k1), i1},
    Hit{w2, Blend.px(q2, t, px, py1, k2), i2}, Hit{w3, Blend.px(q3, t, px1, py1, k3), i3},
    Bool.or(mixed, Bool.or(Bool.or(q0, q1), Bool.or(q2, q3)))}

# The transparent triangles blended over the four blocks from (px, py)
# in the list's order, one flat loop; then their images.
def Blend.go(
  bs: Tris, +px: F32, +py: F32, +b0: Blk, +b1: Blk, +b2: Blk, +b3: Blk
) -> Image:
  match bs:
    case TNil{}:
      Qua{Blk.four(b0), Blk.four(b1), Blk.four(b2), Blk.four(b3)}
    case TCons{t, n}:
      +px1 = (px + 2.0 : F32)
      +py1 = (py + 2.0 : F32)
      Blend.go(n, px, py, Blend.step(t, px, py, b0), Blend.step(t, px1, py, b1),
        Blend.step(t, px, py1, b2), Blend.step(t, px1, py1, b3))

# The block's colours: its hits, the sky where none.
def Blk.fill(+b: Blk, +x: U32, +y: U32, +sky: Sky) -> Blk:
  Blk{h0, h1, h2, h3, mixed} = b
  Hit{w0, c0, i0} = h0
  Hit{w1, c1, i1} = h1
  Hit{w2, c2, i2} = h2
  Hit{w3, c3, i3} = h3
  +x1 = (x + 1 : U32)
  +y1 = (y + 1 : U32)
  Blk{Hit{w0, Blk.at(U32.is_eq(i0, 0), c0, x, y, sky), i0},
    Hit{w1, Blk.at(U32.is_eq(i1, 0), c1, x1, y, sky), i1},
    Hit{w2, Blk.at(U32.is_eq(i2, 0), c2, x, y1, sky), i2},
    Hit{w3, Blk.at(U32.is_eq(i3, 0), c3, x1, y1, sky), i3}, mixed}

# The triangle i over the block's four pixel centres from (px, py):
# the planes step by a column and a row.
def Blk.step(+t: Tri, +i: U32, +px: F32, +py: F32, +b: Blk) -> Blk:
  Tri{a0, b0, c0, a1, b1, c1, wc, wu, wv, rc, ru, rv, gc, gu, gv, bc, bu, bv,
    m, al, bx0, by0, bx1, by1} = t
  Blk{h0, h1, h2, h3, mixed} = b
  Hit{w0, _, _} = h0
  Hit{w1, _, _} = h1
  Hit{w2, _, _} = h2
  Hit{w3, _, _} = h3
  +l0 = (a0 * px + b0 * py + c0 + 0.002 : F32)
  +l1 = (a1 * px + b1 * py + c1 + 0.002 : F32)
  +w = (wc + wu * px + wv * py : F32)
  +px1 = (px + 1.0 : F32)
  +py1 = (py + 1.0 : F32)
  Blk{Blk.hit(Bool.and(Tri.in(l0, l1), (w > w0 : F32)), t, w, i, px, py, h0),
    Blk.hit(Bool.and(Tri.in((l0 + a0 : F32), (l1 + a1 : F32)),
        (w + wu > w1 : F32)), t, (w + wu : F32), i, px1, py, h1),
    Blk.hit(Bool.and(Tri.in((l0 + b0 : F32), (l1 + b1 : F32)),
        (w + wv > w2 : F32)), t, (w + wv : F32), i, px, py1, h2),
    Blk.hit(Bool.and(Tri.in((l0 + a0 + b0 : F32), (l1 + a1 + b1 : F32)),
        (w + wu + wv > w3 : F32)), t, (w + wu + wv : F32), i, px1, py1, h3), mixed}

# The nearest opaque triangle of the tile's list over the four blocks
# from (px, py), the entries counted from i, one flat loop: an entry is
# read once for the sixteen pixels; then the sky, the blends.
def Blk.go(
  cs: Tris, bs: Tris, +i: U32, +px: F32, +py: F32, +x: U32, +y: U32, +sa: Sky,
  +sb: Sky, +b0: Blk, +b1: Blk, +b2: Blk, +b3: Blk
) -> Image:
  match cs:
    case TNil{}:
      +x1 = (x + 2 : U32)
      +y1 = (y + 2 : U32)
      Blend.go(bs, px, py, Blk.fill(b0, x, y, sa), Blk.fill(b1, x1, y, sb),
        Blk.fill(b2, x, y1, sa), Blk.fill(b3, x1, y1, sb))
    case TCons{t, n}:
      +px1 = (px + 2.0 : F32)
      +py1 = (py + 2.0 : F32)
      Blk.go(n, bs, (i + 1 : U32), px, py, x, y, sa, sb, Blk.step(t, i, px, py, b0),
        Blk.step(t, i, px1, py, b1), Blk.step(t, i, px, py1, b2),
        Blk.step(t, i, px1, py1, b3))

# Four blocks under the skies of their two column pairs.
def Tile.b4(+cs: Tris, +bs: Tris, +per: Bool, +x: U32, +y: U32, +sky: Sky) -> Image:
  +b = {Blk{Hit{0.0, 0, 0}, Hit{0.0, 0, 0}, Hit{0.0, 0, 0}, Hit{0.0, 0, 0}, False{}} : Blk}
  Blk.go(cs, bs, 1, (U32.to_f32(x) + 0.5 : F32), (U32.to_f32(y) + 0.5 : F32), x, y,
    Sky.col(per, x, sky), Sky.col(per, (x + 2 : U32), sky), b, b, b, b)

def Tile.b8(+cs: Tris, +bs: Tris, +per: Bool, +x: U32, +y: U32, +sky: Sky) -> Image:
  +x1 = (x + 4 : U32)
  +y1 = (y + 4 : U32)
  Qua{Tile.b4(cs, bs, per, x, y, sky), Tile.b4(cs, bs, per, x1, y, sky),
    Tile.b4(cs, bs, per, x, y1, sky), Tile.b4(cs, bs, per, x1, y1, sky)}

# The tile's lists freed after its pixels read them, one flat loop (as
# dead parameters, the runtime's sink frees them 0.55 ms a frame slower).
def Tile.fin(img: Image, cs: Tris, bs: Tris) -> Image:
  match cs bs:
    case TCons{_, n} _:
      Tile.fin(img, n, bs)
    case TNil{} TCons{_, n}:
      Tile.fin(img, TNil{}, n)
    case TNil{} TNil{}:
      img

def Tile.b16(
  +cs: Tris, +bs: Tris, +per: Bool, +x: U32, +y: U32, +sky: Sky
) -> Image:
  +x1 = (x + 8 : U32)
  +y1 = (y + 8 : U32)
  Qua{Tile.b8(cs, bs, per, x, y, sky), Tile.b8(cs, bs, per, x1, y, sky),
    Tile.b8(cs, bs, per, x, y1, sky), Tile.b8(cs, bs, per, x1, y1, sky)}

# A plain tile (no triangle, nothing crossing) is one Pix; else its
# pixels over its lists.
def Tile.pick(
  plain: Bool, +cs: Tris, +bs: Tris, +per: Bool, +x: U32, +y: U32, +sky: Sky
) -> Image:
  match plain:
    case True{}:
      Pix{Sky.at(x, y, sky)}
    case False{}:
      Tile.fin(Tile.b16(cs, bs, per, x, y, sky), cs, bs)

def Tile.fate(f: Filt, +per: Bool, +x: U32, +y: U32, +sky: Sky) -> Image:
  Filt{n, cs, bs} = f
  Tile.pick(Bool.and(U32.is_eq(n, 0), Bool.not(per)), cs, bs, per, x, y, sky)

# A tile of the cell's borrowed list: its sky, its own lists, then its
# pixels; the last frame's tile (old, a dead parameter) is sunk on entry.
def Tile.go(cs: Tris, +x: U32, +y: U32, old: Four) -> Image:
  +sky = Sky.of(x, y, 16)
  Tile.fate(Tris.filter(cs, x, y, (x + 15 : U32), (y + 15 : U32), Filt{0, TNil{}, TNil{}}),
    Sky.mixed(sky, x, y, 16), x, y, sky)

# The last frame's image of a region as its four quadrants (a plain
# one: four of its pixel).
def Image.open(old: Image) -> Four:
  match old:
    case Pix{+c}:
      Four{Pix{c}, Pix{c}, Pix{c}, Pix{c}}
    case Qua{a, b, c, d}:
      Four{a, b, c, d}

# k levels of four-way forks over the cell's borrowed list down to its
# tiles; the last frame's image goes down quadrant by quadrant and
# each tile sinks its own.
def Cell.fork(+k: Nat, +cs: Tris, +x: U32, +y: U32, old: Four) -> Image:
  match k:
    case 0n:
      Tile.go(cs, x, y, old)
    case 1n+e:
      Four{oa, ob, oc, od} = old
      +h = U32.shln(16, e)
      +x1 = (x + h : U32)
      +y1 = (y + h : U32)
      a b c d = Cell.fork(e, cs, x, y, Image.open(oa)) Cell.fork(e, cs, x1, y, Image.open(ob))
        Cell.fork(e, cs, x, y1, Image.open(oc)) Cell.fork(e, cs, x1, y1, Image.open(od))
      Qua{a, b, c, d}

# An empty region of 64 << k at (x, y): black off the screen, else split
# down to its cells and their tiles (a tile nothing crosses is one Pix).
def Frame.sky(+k: Nat, on: Bool, +x: U32, +y: U32, old: Four) -> Image:
  match k on:
    case 0n True{}:
      Cell.fork(2n, TNil{}, x, y, old)
    case 1n+e True{}:
      Four{oa, ob, oc, od} = old
      +h = U32.shln(64, e)
      +x1 = (x + h : U32)
      +y1 = (y + h : U32)
      a b c d = Frame.sky(e, True{}, x, y, Image.open(oa))
        Frame.sky(e, (x1 < 1920 : U32), x1, y, Image.open(ob))
        Frame.sky(e, (y1 < 1200 : U32), x, y1, Image.open(oc))
        Frame.sky(e, ((x1 < 1920) && (y1 < 1200) : U32), x1, y1, Image.open(od))
      Qua{a, b, c, d}
    case _ False{}:
      Pix{0}

# A region of the borrowed tree: an empty one is its sky, a cell is its
# tiles, a node forks.
def Frame.node(c: Cells, +k: Nat, +x: U32, +y: U32, old: Four) -> Image:
  match c:
    case CNil{}:
      Frame.sky(k, ((x < 1920) && (y < 1200) : U32), x, y, old)
    case CLeaf{_, ts}:
      Cell.fork(2n, ts, x, y, old)
    case CQua{tl, tr, bl, br}:
      match k:
        case 0n:
          Pix{0}
        case 1n+e:
          Four{oa, ob, oc, od} = old
          +h = U32.shln(64, e)
          +x1 = (x + h : U32)
          +y1 = (y + h : U32)
          a b c d = Frame.node(tl, e, x, y, Image.open(oa)) Frame.node(tr, e, x1, y, Image.open(ob))
            Frame.node(bl, e, x, y1, Image.open(oc)) Frame.node(br, e, x1, y1, Image.open(od))
          Qua{a, b, c, d}

# The frame over the last one (dropped tile by tile inside it): the
# bang borrows the tree, which comes back for the host to drop.
def Frame.show(+cells: Cells, old: Image) -> Image & Cells:
  (Frame.node!(cells, 5n, 0, 0, Image.open(old)), cells)


# Sound
# -----

# The sound is Bend's: 14 clips are synthesized at launch and 7 read
# from WAV files (media/slash_bros_3d) into one store of samples, a
# mixer of up to 24 voices renders 512-frame stereo blocks at 48 kHz;
# only the transport (Audio.open/write/close) is native. A clip: its first sample in the
# store, its frames, its rate and its channels (1 or 2).
type Clip is Data:
  Clip{start: U32, frames: U32, rate: U32, ch: U32}

# A voice: its clip, its place in frames, its step a frame, its gains
# on the left and the right, does it loop.
type Voice is Data:
  Voice{clip: Clip, pos: F32, step: F32, gl: F32, gr: F32, loop: Bool}

# A cue: the clip to play (0-13 synthesized, 14 guaraná, 15 sha, 16
# needle, 17 dash, 18 parry), its gain, its pan, its rate, looping.
type Cue is Data:
  Cue{kind: U32, gain: F32, pan: F32, rate: F32, loop: Bool}

# The sound: the device (none when it failed to open), the store, the
# clips by kind, the voices (oldest first), the voices before the last
# block (kept while its write may be dropped), the last block rendered,
# the frames the device held at the clock stamp.
type Sound is Type:
  Sound{dev: Maybe<Audio>, pcm: Array<F32>, +bank: List<&2, Clip>, +voices: List<&2, Voice>,
    +prev: List<&2, Voice>, +block: List<&2, F32>, +queued: U32, +stamp: Nat}

# The chunk tags of a WAV walk.
type Tag is Data:
  Head{}
  Fmt{}
  Body{}
  Skip{}

# A WAV's format: its kind (1 PCM16, 3 float32), channels, rate, bits.
type Wave is Data:
  Wave{kind: U32, ch: U32, rate: U32, bits: U32}

def Synth.noise(+i: U32) -> F32:
  +a = (U32.xor(i, (i >> 16n)) * 2146121005 : U32)
  +b = (U32.xor(a, (a >> 15n)) * 2221713035 : U32)
  (U32.to_f32((U32.xor(b, (b >> 16n)) .&. 65535 : U32)) / 32767.5 - 1.0 : F32)

# Sample i of clip kind (65536 at 48 kHz): the original's hiss, swish,
# thud and bell mixed by kind (0 swish, 1 swish and bell, 2 swish and
# thud, 3 a chirp, 4 thud, 5 bell, 6 heavy, 7 a soft swish, 8 the jump
# chirp, 9 a soft thud, 10 the death boom, 11 the FM voice, 12 a soft
# bell), under an attack and a squared tail; 13 the ambient drone.
def Synth.sample(+kind: U32, +i: U32) -> F32:
  +u = (U32.to_f32(i) / 65536.0 : F32)
  +t = (U32.to_f32(i) / 48000.0 : F32)
  +attack = Math.min(1.0, (t * 240.0 : F32))
  +tail = ((1.0 - u) * (1.0 - u) : F32)
  +hiss = (Synth.noise(i) * 0.65 + Synth.noise((i / 3 : U32)) * 0.35 : F32)
  +swish = ((hiss * F32.exp((0.0 - t * 18.0 : F32)) * 0.32)
    + (F32.sin((t * (11000.0 - t * 6500.0) : F32)) * F32.exp((0.0 - t * 27.0 : F32)) * 0.08) : F32)
  +thud = ((F32.sin((t * (680.0 - t * 230.0) : F32)) * F32.exp((0.0 - t * 13.0 : F32)) * 0.38)
    + (hiss * F32.exp((0.0 - t * 48.0 : F32)) * 0.28) : F32)
  +bell = ((F32.sin((t * 6911.5 : F32)) + (F32.sin((t * 10361.3 : F32)) * 0.45)
    + (F32.sin((t * 15742.1 : F32)) * 0.22)) * F32.exp((0.0 - t * 4.0 : F32)) * 0.17 : F32)
  +chirp = (F32.sin((t * (1900.0 + t * 14000.0) : F32)) * F32.exp((0.0 - t * 10.0 : F32)) * 0.18 : F32)
  +hop = (F32.sin((t * (2100.0 + t * 6200.0) : F32)) * F32.exp((0.0 - t * 26.0 : F32)) * 0.14 : F32)
  +boom = (((F32.sin((t * (540.0 - t * 190.0) : F32)) * 0.32) + (hiss * 0.25))
    * F32.exp((0.0 - t * 2.8 : F32)) + (bell * 0.6) : F32)
  +voice = (((F32.sin((t * 410.0 + F32.sin((t * 720.0 : F32)) * 3.0 : F32)) * 0.20) + (hiss * 0.1))
    * F32.sin((u * 3.1415927 : F32)) : F32)
  +drone = ((F32.sin((u * 1884.9556 : F32)) + (F32.sin((u * 2827.4334 : F32)) * 0.4)
    + (F32.sin((u * 3769.9111 : F32)) * 0.18)) * 0.075 : F32)
  +value = Math.pick(U32.is_eq(kind, 0), swish,
    Math.pick(U32.is_eq(kind, 1), (swish * 0.7 + bell * 0.35 : F32),
    Math.pick(U32.is_eq(kind, 2), (swish * 1.2 + thud * 0.4 : F32),
    Math.pick(U32.is_eq(kind, 3), (chirp + swish * 0.5 : F32),
    Math.pick(U32.is_eq(kind, 4), thud,
    Math.pick(U32.is_eq(kind, 5), bell,
    Math.pick(U32.is_eq(kind, 6), (thud * 1.4 + bell * 0.8 : F32),
    Math.pick(U32.is_eq(kind, 7), (swish * 0.65 : F32),
    Math.pick(U32.is_eq(kind, 8), hop,
    Math.pick(U32.is_eq(kind, 9), (thud * 0.38 : F32),
    Math.pick(U32.is_eq(kind, 10), boom,
    Math.pick(U32.is_eq(kind, 11), voice, (bell * 0.60 : F32)))))))))))))
  Math.pick(U32.is_eq(kind, 13), drone, (value * attack * tail : F32))

# k samples of a kind from i into the store at `at`.
def Synth.fill(k: Nat, +kind: U32, +i: U32, +at: U32, pcm: Array<F32>) -> Array<F32>:
  match k:
    case 0n:
      pcm
    case 1n+j:
      Synth.fill(j, kind, (i + 1 : U32), at, Array.set(F32, pcm, (at + i : U32), Synth.sample(kind, i)))

# The clips under n synthesized, each 65536 samples at kind x 65536.
def Synth.all(+n: Nat, pcm: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      pcm
    case 1n+k:
      Synth.all(k, Synth.fill(U32.to_nat(65536), U32.from_nat(k), 0, (U32.from_nat(k) * 65536 : U32), pcm))

# The little-endian words at the head of the bytes (0 past the end).
def Wav.u16(+b: List<&2, U32>) -> U32:
  match b:
    case Con{x, Con{y, _}}:
      (x .|. (y << 8n) : U32)
    case _:
      0

def Wav.u32(+b: List<&2, U32>) -> U32:
  match b:
    case Con{x, Con{y, Con{z, Con{w, _}}}}:
      (x .|. (y << 8n) .|. (z << 16n) .|. (w << 24n) : U32)
    case _:
      0

def Wav.skip(n: Nat, b: List<&2, U32>) -> List<&2, U32>:
  match n b:
    case 0n _:
      b
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{_, rest}:
      Wav.skip(k, rest)

# A float from its bits (a denormal keeps its scale; NaN and inf are
# not audio and are not special-cased).
def Wav.float(+w: U32) -> F32:
  +e = ((w >> 23n) .&. 255 : U32)
  +m = ((w .&. 8388607 : U32) .|. Math.word(U32.is_eq(e, 0), 0, 8388608) : U32)
  +v = (U32.to_f32(m) * F32.pow(2.0, Math.pick(U32.is_eq(e, 0), (0.0 - 149.0 : F32),
    (U32.to_f32(e) - 150.0 : F32))) : F32)
  Math.pick((w >= 2147483648 : U32), (0.0 - v : F32), v)

def Wav.signed(+v: U32) -> F32:
  ((U32.to_f32(v) - Math.pick((v >= 32768 : U32), 65536.0, 0.0)) / 32768.0 : F32)

# n PCM16 samples from the bytes into the store from `at`.
def Wav.s16(n: Nat, b: List<&2, U32>, +at: U32, pcm: Array<F32>) -> Array<F32>:
  match n b:
    case 0n _:
      pcm
    case 1n+k Con{lo, Con{hi, rest}}:
      Wav.s16(k, rest, (at + 1 : U32), Array.set(F32, pcm, at, Wav.signed((lo .|. (hi << 8n) : U32))))
    case 1n+k _:
      pcm

# n float32 samples from the bytes into the store from `at`.
def Wav.f32(n: Nat, b: List<&2, U32>, +at: U32, pcm: Array<F32>) -> Array<F32>:
  match n b:
    case 0n _:
      pcm
    case 1n+k Con{x, Con{y, Con{z, Con{w, rest}}}}:
      Wav.f32(k, rest, (at + 1 : U32), Array.set(F32, pcm, at,
        Wav.float((x .|. (y << 8n) .|. (z << 16n) .|. (w << 24n) : U32))))
    case 1n+k _:
      pcm

def Wav.samples(short: Bool, n: Nat, b: List<&2, U32>, +at: U32, pcm: Array<F32>) -> Array<F32>:
  match short:
    case True{}:
      Wav.s16(n, b, at, pcm)
    case False{}:
      Wav.f32(n, b, at, pcm)

# The data chunk of `size` bytes decoded into the store at `at` (PCM16
# or float32, else nothing); the clip.
def Wav.data(+f: Wave, +size: U32, b: List<&2, U32>, +at: U32, pcm: Array<F32>) -> Array<F32> & Clip:
  Wave{kind, ch, rate, bits} = f
  +short = U32.is_eq(kind, 1)
  +ok = ((short && U32.is_eq(bits, 16)) || (U32.is_eq(kind, 3) && U32.is_eq(bits, 32)))
  +n = Math.word(ok, (size / (bits / 8) : U32), 0)
  (Wav.samples(short, U32.to_nat(n), b, at, pcm),
    Clip{at, (n / Math.word((ch > 0 : U32), ch, 1) : U32), rate, Math.word((ch > 0 : U32), ch, 1)})

# The format chunk (an extensible one's kind sits at 24).
def Wav.fmt(+b: List<&2, U32>) -> Wave:
  +kind = Wav.u16(b)
  Wave{Math.word(U32.is_eq(kind, 65534), Wav.u16(Wav.skip(24n, b)), kind), Wav.u16(Wav.skip(2n, b)),
    Wav.u32(Wav.skip(4n, b)), Wav.u16(Wav.skip(14n, b))}

def Wav.tag.of(fmt: Bool, data: Bool) -> Tag:
  match fmt data:
    case True{} _:
      Fmt{}
    case _ True{}:
      Body{}
    case _ _:
      Skip{}

def Wav.tag(+w: U32) -> Tag:
  Wav.tag.of(U32.is_eq(w, 544501094), U32.is_eq(w, 1635017060))

# The chunks walked on a fuel: at a head its tag and size are read; the
# fmt chunk gives the format; the data chunk is decoded and ends the
# walk; any other is skipped (padded to even). Past the fuel or the
# bytes, an empty clip.
def Wav.walk(
  fuel: Nat, tag: Tag, +size: U32, +b: List<&2, U32>, +f: Wave, +at: U32, pcm: Array<F32>
) -> Array<F32> & Clip:
  match fuel tag b:
    case 0n _ _:
      (pcm, Clip{at, 0, 48000, 1})
    case 1n+k _ Nil{}:
      (pcm, Clip{at, 0, 48000, 1})
    case 1n+k Head{} _:
      Wav.walk(k, Wav.tag(Wav.u32(b)), Wav.u32(Wav.skip(4n, b)), Wav.skip(8n, b), f, at, pcm)
    case 1n+k Fmt{} _:
      Wav.walk(k, Head{}, 0, Wav.skip(U32.to_nat((size + (size .&. 1) : U32)), b), Wav.fmt(b), at, pcm)
    case 1n+k Skip{} _:
      Wav.walk(k, Head{}, 0, Wav.skip(U32.to_nat((size + (size .&. 1) : U32)), b), f, at, pcm)
    case 1n+k Body{} _:
      Wav.data(f, size, b, at, pcm)

# A WAV's bytes decoded into the store at `at`; the clip.
def Wav.load(b: List<&2, U32>, +at: U32, pcm: Array<F32>) -> Array<F32> & Clip:
  Wav.walk(64n, Head{}, 0, Wav.skip(12n, b), Wave{1, 1, 48000, 16}, at, pcm)

def Asset.dir(near: Bool) -> String:
  match near:
    case True{}:
      "../../media/slash_bros_3d/"
    case False{}:
      "media/slash_bros_3d/"

def Asset.got(r: Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  match r:
    case Done{b}:
      b
    case Fail{_}:
      Nil{}

# The bytes read (up to 1 MB), the file closed; none on a failure.
def Asset.read(m: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (f, r) = m
  do IO<List<&2, U32>>:
    Unit <- File.close(f)
    IO.pure(List<&2, U32>, Asset.got(r))

# An asset opened from the cwd, else from the demo's dir; missing, a
# warning and no bytes.
def Asset.opened(
  tries: Nat, +name: String, r: Result<&1, &1, U32 & String, File>
) -> IO(List<&2, U32>):
  match tries r:
    case _ Done{f}:
      do IO<List<&2, U32>>:
        m : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1048576)
        Asset.read(m)
    case 0n Fail{_}:
      do IO<List<&2, U32>>:
        Unit <- IO.print_err("sound: " ++ name ++ " is missing (silent)")
        IO.pure(List<&2, U32>, Nil{})
    case 1n+k Fail{_}:
      do IO<List<&2, U32>>:
        r2 : Result<&1, &1, U32 & String, File> <- File.open(Asset.dir(True{}) ++ name, "r")
        Asset.opened(k, name, r2)

def Asset.bytes(+name: String) -> IO(List<&2, U32>):
  do IO<List<&2, U32>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(Asset.dir(False{}) ++ name, "r")
    Asset.opened(1n, name, r)

def Asset.wav(name: String, +at: U32, pcm: Array<F32>) -> IO(Array<F32> & Clip):
  do IO<Array<F32> & Clip>:
    b : List<&2, U32> <- Asset.bytes(name)
    IO.pure(Array<F32> & Clip, Wav.load(b, at, pcm))

def Clip.size(+c: Clip) -> U32:
  Clip{_, frames, _, ch} = c
  (frames * ch : U32)

def Clip.frames(+c: Clip) -> U32:
  Clip{_, frames, _, _} = c
  frames

# The named files decoded one after another into the store, each after
# the last clip; the clips, last first.
def Asset.each(
  names: List<String>, +at: U32, clips: List<&2, Clip>, r: Array<F32> & Clip
) -> IO(Array<F32> & List<&2, Clip>):
  match names:
    case Nil{}:
      (pcm, clip) = r
      IO.pure(Array<F32> & List<&2, Clip>, (pcm, Con{clip, clips}))
    case Con{name, rest}:
      (pcm, +clip) = r
      +at2 = (at + Clip.size(clip) : U32)
      do IO<Array<F32> & List<&2, Clip>>:
        r2 : Array<F32> & Clip <- Asset.wav(name, at2, pcm)
        Asset.each(rest, at2, Con{clip, clips}, r2)

# The synthesized clips 0 to n - 1 before the rest.
def Bank.synth(+n: Nat, rest: List<&2, Clip>) -> List<&2, Clip>:
  match n:
    case 0n:
      rest
    case 1n+k:
      Bank.synth(k, Con{Clip{(U32.from_nat(k) * 65536 : U32), 65536, 48000, 1}, rest})

# The bank by kind from the files loaded (last first, after the
# synthesized region's stand-in): the three guaraná parts are one
# gapless clip (they sit end to end in the store).
def Bank.build(files: List<&2, Clip>) -> List<&2, Clip>:
  match files:
    case Con{parry, Con{dash, Con{needle, Con{sha, Con{c, Con{b, Con{a, _}}}}}}}:
      Clip{start, fa, rate, ch} = a
      Bank.synth(14n, [Clip{start, (fa + Clip.frames(b) + Clip.frames(c) : U32), rate, ch}, sha,
        needle, dash, parry])
    case _:
      Bank.synth(14n, Nil{})

def Bank.at(n: Nat, +bank: List<&2, Clip>) -> Clip:
  match n bank:
    case _ Nil{}:
      Clip{0, 0, 48000, 1}
    case 0n Con{c, _}:
      c
    case 1n+k Con{_, rest}:
      Bank.at(k, rest)

# A voice of a clip: its step a frame is the clip's rate over the
# device's times the rate asked; the pan keeps the centre's level and
# never lifts a side.
def Voice.of(+clip: Clip, +gain: F32, +pan: F32, +rate: F32, loop: Bool) -> Voice:
  Clip{_, _, crate, _} = clip
  Voice{clip, 0.0, (U32.to_f32(crate) / 48000.0 * rate : F32), (gain * Math.min(1.0, (1.0 - pan : F32)) : F32),
    (gain * Math.min(1.0, (1.0 + pan : F32)) : F32), loop}

def Voices.count(+vs: List<&2, Voice>) -> U32:
  match vs:
    case Nil{}:
      0
    case Con{_, rest}:
      (1 + Voices.count(rest) : U32)

def Voices.snoc(vs: List<&2, Voice>, v: Voice) -> List<&2, Voice>:
  match vs:
    case Nil{}:
      [v]
    case Con{x, rest}:
      Con{x, Voices.snoc(rest, v)}

# The oldest voice that does not loop, stolen.
def Voices.steal(vs: List<&2, Voice>) -> List<&2, Voice>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Voice{clip, pos, step, gl, gr, True{}}, rest}:
      Con{Voice{clip, pos, step, gl, gr, True{}}, Voices.steal(rest)}
    case Con{Voice{clip, pos, step, gl, gr, False{}}, rest}:
      rest

# A voice added (none for an empty clip), the oldest stolen at 24.
def Voices.put(ok: Bool, full: Bool, v: Voice, vs: List<&2, Voice>) -> List<&2, Voice>:
  match ok full:
    case False{} _:
      vs
    case True{} True{}:
      Voices.snoc(Voices.steal(vs), v)
    case True{} False{}:
      Voices.snoc(vs, v)

def Voices.keep(gone: Bool, v: Voice, rest: List<&2, Voice>) -> List<&2, Voice>:
  match gone:
    case True{}:
      rest
    case False{}:
      Con{v, rest}

# The voices a block (512 frames) later: a looping one wraps, one past
# its clip's end is gone.
def Voices.step(+vs: List<&2, Voice>) -> List<&2, Voice>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Voice{clip, pos, step, gl, gr, loop}, rest}:
      Clip{start, frames, rate, ch} = clip
      +fr = U32.to_f32(frames)
      +next = (pos + step * 512.0 : F32)
      +over = (next >= fr : F32)
      Voices.keep((over && Bool.not(loop)),
        Voice{Clip{start, frames, rate, ch}, Math.pick((over && loop), F32.mod(next, fr), next), step, gl, gr, loop},
        Voices.step(rest))

# The sample after i1 - 1: wrapped to 0 for a loop, else held at the
# last.
def Mix.next(loop: Bool, +i1: U32, +frames: U32) -> U32:
  match loop:
    case True{}:
      Math.word((i1 >= frames : U32), 0, i1)
    case False{}:
      Math.word((i1 >= frames : U32), (frames - 1 : U32), i1)

def Mix.wrap(loop: Bool, +c: F32, +frames: U32) -> F32:
  Math.pick((loop && (c >= U32.to_f32(frames) : F32)), (c - U32.to_f32(frames) : F32), c)

# A frame's left and right into the block at frame i: the store comes
# back with the block.
def Mix.w1(+i: U32, +vr: F32, pcm: Array<F32>, r: Array<F32> & F32) -> Array<F32> & Array<F32>:
  (out, o) = r
  (pcm, Array.set(F32, out, (2 * i + 1 : U32), (o + vr : F32)))

def Mix.w0(+i: U32, +vl: F32, +vr: F32, pcm: Array<F32>, r: Array<F32> & F32) -> Array<F32> & Array<F32>:
  (out, o) = r
  Mix.w1(i, vr, pcm, Array.get(F32, Array.set(F32, out, (2 * i : U32), (o + vl : F32)), (2 * i + 1 : U32)))

# The right sample of the frame at a: the left one again for a mono
# clip (no read).
def Mix.right(mono: Bool, pcm: Array<F32>, +a: U32, +l: F32) -> Array<F32> & F32:
  match mono:
    case True{}:
      (pcm, l)
    case False{}:
      Array.get(F32, pcm, (a + 1 : U32))

# A clip's sample at the cursor (its floor i0 and fraction f,
# interpolated with the next frame; silent past the end) into frame i:
# four reads (l0, r0, l1, r1), a step of ch samples a frame.
def Mix.t4(
  +i: U32, +f: F32, +live: F32, +gl: F32, +gr: F32, +l0: F32, +r0: F32, +l1: F32, out: Array<F32>,
  r: Array<F32> & F32
) -> Array<F32> & Array<F32>:
  (pcm, r1) = r
  Mix.w0(i, ((l0 + (l1 - l0) * f) * live * gl : F32), ((r0 + (r1 - r0) * f) * live * gr : F32), pcm,
    Array.get(F32, out, (2 * i : U32)))

def Mix.t3(
  +i: U32, +f: F32, +live: F32, +gl: F32, +gr: F32, +l0: F32, +r0: F32, +a1: U32, mono: Bool,
  out: Array<F32>, r: Array<F32> & F32
) -> Array<F32> & Array<F32>:
  (pcm, +l1) = r
  Mix.t4(i, f, live, gl, gr, l0, r0, l1, out, Mix.right(mono, pcm, a1, l1))

def Mix.t2(
  +i: U32, +f: F32, +live: F32, +gl: F32, +gr: F32, +l0: F32, +a1: U32, mono: Bool, out: Array<F32>,
  r: Array<F32> & F32
) -> Array<F32> & Array<F32>:
  (pcm, r0) = r
  Mix.t3(i, f, live, gl, gr, l0, r0, a1, mono, out, Array.get(F32, pcm, a1))

def Mix.t1(
  +i: U32, +f: F32, +live: F32, +gl: F32, +gr: F32, +a0: U32, +a1: U32, +mono: Bool, out: Array<F32>,
  r: Array<F32> & F32
) -> Array<F32> & Array<F32>:
  (pcm, +l0) = r
  Mix.t2(i, f, live, gl, gr, l0, a1, mono, out, Mix.right(mono, pcm, a0, l0))

def Mix.t0(
  +i: U32, +c: F32, +start: U32, +frames: U32, loop: Bool, +gl: F32, +gr: F32, +ch: U32,
  ro: Array<F32> & Array<F32>
) -> Array<F32> & Array<F32>:
  (pcm, out) = ro
  +i0 = F32.to_u32(c)
  +f = (c - U32.to_f32(i0) : F32)
  +hit = (i0 < frames : U32)
  +a0 = (start + ch * Math.word(hit, i0, (frames - 1 : U32)) : U32)
  Mix.t1(i, f, Math.pick(hit, 1.0, 0.0), gl, gr, a0, (start + ch * Mix.next(loop, (i0 + 1 : U32), frames) : U32),
    U32.is_eq(ch, 1), out, Array.get(F32, pcm, a0))

# k frames of a voice from frame i at the cursor c into the block, one
# flat loop.
def Mix.run(
  k: Nat, +i: U32, +c: F32, +step: F32, +start: U32, +frames: U32, +loop: Bool, +gl: F32, +gr: F32,
  +ch: U32, ro: Array<F32> & Array<F32>
) -> Array<F32> & Array<F32>:
  match k:
    case 0n:
      ro
    case 1n+j:
      Mix.run(j, (i + 1 : U32), Mix.wrap(loop, (c + step : F32), frames), step, start, frames, loop, gl,
        gr, ch, Mix.t0(i, c, start, frames, loop, gl, gr, ch, ro))

def Mix.voices(+vs: List<&2, Voice>, ro: Array<F32> & Array<F32>) -> Array<F32> & Array<F32>:
  match vs:
    case Nil{}:
      ro
    case Con{Voice{clip, pos, step, gl, gr, loop}, rest}:
      Clip{start, frames, _, ch} = clip
      Mix.voices(rest, Mix.run(U32.to_nat(512), 0, pos, step, start, frames, loop, gl, gr, ch, ro))

# The block's samples from i down as a list, each clamped.
def Mix.list(k: Nat, +i: U32, acc: List<&2, F32>, r: Array<F32> & F32) -> List<&2, F32>:
  match k:
    case 0n:
      (out, x) = r
      Con{Math.clamp(x, (0.0 - 1.0 : F32), 1.0), acc}
    case 1n+j:
      (out, x) = r
      Mix.list(j, (i - 1 : U32), Con{Math.clamp(x, (0.0 - 1.0 : F32), 1.0), acc},
        Array.get(F32, out, (i - 1 : U32)))

def Mix.fin(
  dev: Maybe<Audio>, +bank: List<&2, Clip>, +voices: List<&2, Voice>, +queued: U32, +stamp: Nat,
  ro: Array<F32> & Array<F32>
) -> Sound:
  (pcm, out) = ro
  Sound{dev, pcm, bank, Voices.step(voices), voices,
    Mix.list(U32.to_nat(1023), 1023, Nil{}, Array.get(F32, out, 1023)), queued, stamp}

# A block rendered from the voices: the mix of every voice into a fresh
# block of 1024 samples, listed; the voices stepped, the old ones kept.
def Mix.render(s: Sound) -> Sound:
  Sound{dev, pcm, bank, voices, _, _, queued, stamp} = s
  Mix.fin(dev, bank, voices, queued, stamp, Mix.voices(voices, (pcm, Array.new(F32, 10n, 0.0))))

# A cue started: its voice joins the voices (the oldest that does not
# loop stolen at 24; an empty clip is nothing).
def Sound.play(s: Sound, +c: Cue) -> Sound:
  Sound{dev, pcm, bank, voices, prev, block, queued, stamp} = s
  Cue{kind, gain, pan, rate, loop} = c
  +clip = Bank.at(U32.to_nat(kind), bank)
  Sound{dev, pcm, bank, Voices.put((Clip.frames(clip) > 0 : U32), (Voices.count(voices) >= 24 : U32),
      Voice.of(clip, gain, pan, rate, loop), voices), prev, block, queued, stamp}

def Sound.cues(cues: List<&2, Cue>, s: Sound) -> Sound:
  match cues:
    case Nil{}:
      s
    case Con{c, rest}:
      Sound.cues(rest, Sound.play(s, c))

# The write's answer taken: the frames queued now, at this clock; a
# dropped block (the queue was full: over 3584 frames after the write)
# leaves the voices where they were.
def Sound.after(
  old: Maybe<Audio>, pcm: Array<F32>, +bank: List<&2, Clip>, +voices: List<&2, Voice>,
  +prev: List<&2, Voice>, +now: Nat, r: Audio & U32
) -> Sound & Audio:
  (dev, +q) = r
  (Sound{old, pcm, bank, Bool.pick(List<&2, Voice>, (q > 3584 : U32), prev, voices), prev, Nil{},
    q, now}, dev)

def Sound.write(dev: Audio, s: Sound, +now: Nat) -> IO(Sound & Audio):
  Sound{old, pcm, bank, voices, prev, block, _, _} = s
  do IO<Sound & Audio>:
    r : Audio & U32 <- Audio.write(dev, block)
    IO.pure(Sound & Audio, Sound.after(old, pcm, bank, voices, prev, now, r))

def Sound.fix(s: Sound, dev: Audio) -> Sound:
  Sound{_, pcm, bank, voices, prev, block, queued, stamp} = s
  Sound{Some{dev}, pcm, bank, voices, prev, block, queued, stamp}

def Sound.feed(n: Nat, +now: Nat, sr: Sound & Audio) -> IO(Sound):
  match n:
    case 0n:
      (s, dev) = sr
      IO.pure(Sound, Sound.fix(s, dev))
    case 1n+k:
      (s, dev) = sr
      do IO<Sound>:
        sr2 : Sound & Audio <- Sound.write(dev, Mix.render(s), now)
        Sound.feed(k, now, sr2)

# The device fed: the queue as of now (the last count less 48 frames a
# ms since) under 1024 frames asks for blocks of 512 to reach it, at
# most 8 a frame; paused, none (the device plays silence).
def Sound.serve.go(s: Sound, +now: Nat, paused: Bool) -> IO(Sound):
  Sound{dev, pcm, bank, voices, prev, block, queued, stamp} = s
  match dev:
    case None{}:
      IO.pure(Sound, Sound{None{}, pcm, bank, voices, prev, block, queued, stamp})
    case Some{a}:
      +drained = (U32.from_nat(Nat.sub(now, stamp)) * 48 : U32)
      +est = Math.word((drained < queued : U32), (queued - drained : U32), 0)
      +want = ((1024 - est + 511) / 512 : U32)
      +n = Math.word((paused || (est >= 1024 : U32)), 0, Math.word((want < 8 : U32), want, 8))
      Sound.feed(U32.to_nat(n), now, (Sound{None{}, pcm, bank, voices, prev, block, queued, stamp}, a))

def Sound.serve(s: Sound, cues: List<&2, Cue>, +now: Nat, paused: Bool) -> IO(Sound):
  Sound.serve.go(Sound.cues(cues, s), now, paused)

def Sound.close(s: Sound) -> IO(Unit):
  Sound{dev, _, _, _, _, _, _, _} = s
  match dev:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{a}:
      Audio.close(a)

def Sound.device(r: Result<&1, &1, U32 & String, Audio>) -> IO(Maybe<Audio>):
  match r:
    case Done{a}:
      IO.pure(Maybe<Audio>, Some{a})
    case Fail{(code, text)}:
      do IO<Maybe<Audio>>:
        Unit <- IO.print_err("sound: " ++ text ++ " (silent)")
        IO.pure(Maybe<Audio>, None{})

# The sound made: the ambient drone loops from the start.
def Sound.made(dev: Maybe<Audio>, loaded: Array<F32> & List<&2, Clip>) -> Sound:
  (pcm, files) = loaded
  Sound.play(Sound{dev, pcm, Bank.build(files), Nil{}, Nil{}, Nil{}, 0, 0n},
    Cue{13, 0.28, 0.0, 1.0, True{}})

# The sound opened: the device (or none, with a warning), the 14 clips
# synthesized into the store, the 7 files decoded after them.
def Sound.open() -> IO(Sound):
  do IO<Sound>:
    r : Result<&1, &1, U32 & String, Audio> <- Audio.open(48000)
    dev : Maybe<Audio> <- Sound.device(r)
    loaded : Array<F32> & List<&2, Clip> <- Asset.each(["guarana_a.wav", "guarana_b.wav",
        "guarana_c.wav", "sha_pcm.wav", "needle.wav", "dash.wav", "parry.wav"], 0, Nil{},
      (Synth.all(14n, Array.new(F32, 21n, 0.0)), Clip{0, 917504, 48000, 1}))
    IO.pure(Sound, Sound.made(dev, loaded))

def Cue.add(
  on: Bool, +kind: U32, +gain: F32, +pan: F32, +rate: F32, loop: Bool, acc: List<&2, Cue>
) -> List<&2, Cue>:
  match on:
    case True{}:
      Con{Cue{kind, gain, pan, rate, loop}, acc}
    case False{}:
      acc

# The cues of a tick from a to b (the original's sound.bend): an attack
# starting plays its swing (heavy past a charge of 2, a special's, an
# upward one's, a dash's, else the plain) and the needle (the dash's
# for a side special); a parry the parry clip and the bell, another hit
# the thud; a jump, a landing, a dodge, a death or the win, the boss's
# voice every 240 ticks, the guaraná call as the title gives way to the
# fight, sha on a special every third tick, all panned by x / 15; the
# boss's slam lands a heavy thud, its draw rings the bell, its attacks
# start with its voice.
def Cue.list(+a: Game, +b: Game, acc: List<&2, Cue>) -> List<&2, Cue>:
  Game{t0, _, _, m0, hero0, boss0, f0, _, _, _, _} = a
  Fighter{p1, v1, face1, damage1, guard1, jumps1, action1, age1, inv1, stocks1, grace1, queued1,
    charge1} = hero0
  Boss{_, _, _, _, _, _, state1, _, _, _, _} = boss0
  Game{time, _, _, mode, hero, boss, flash, _, _, _, _} = b
  Fighter{p, v, _, _, _, _, action, age, _, stocks, _, _, charge} = hero
  Boss{q, _, _, _, stun, _, state, bage, _, _, _} = boss
  +changed = U32.is_ne(t0, time)
  +attack = (changed && Act.attack(action) && (U32.is_ne(action1, action) || (age > age1 : U32)))
  +special = Act.special(action)
  +side = (U32.is_eq(action, 20) || U32.is_eq(action, 24))
  +new_hit = (changed && (flash > f0 : U32))
  +death = (stocks < stocks1 : U32)
  +land = ((Vec.y(v1) < (0.0 - 0.03 : F32) : F32) && Bool.not(Fighter.air(p, v)))
  +jump = ((Vec.y(v) > 0.3 : F32) && (Vec.y(v1) <= 0.0 : F32))
  +pan = Math.clamp((Vec.x(p) / 15.0 : F32), (0.0 - 0.7 : F32), 0.7)
  +bpan = Math.clamp((Vec.x(q) / 15.0 : F32), (0.0 - 0.7 : F32), 0.7)
  +kind = Math.word((charge > 2 : U32), 6, Math.word(special, 0, Math.word(Act.up(action), 3,
    Math.word(side, 2, 1))))
  +parried = (new_hit && U32.is_eq(action, 3) && (stun > 0 : U32))
  +bfresh = (changed && U32.is_eq(bage, 0) && U32.is_ne(state, state1))
  Cue.add(attack, kind, 0.63, pan, (0.96 + U32.to_f32((time % 7 : U32)) * 0.013 : F32), False{},
    Cue.add(attack, Math.word(side, 17, 16), 0.44, pan, 1.0, False{},
    Cue.add(parried, 18, 0.60, pan, 1.0, False{},
    Cue.add((new_hit && Bool.not(death)), Math.word(parried, 5, 4), 0.70, pan, 1.0, False{},
    Cue.add((changed && jump), 8, 0.56, pan, 1.0, False{},
    Cue.add((changed && land), 9, 0.65, pan, 1.0, False{},
    Cue.add((changed && U32.is_eq(action, 6) && U32.is_ne(action1, 6)), 7, 0.65, pan, 1.0, False{},
    Cue.add((death || (U32.is_eq(mode, 2) && U32.is_ne(m0, 2))), 10, 0.85, 0.0, 1.0, False{},
    Cue.add((changed && U32.is_ne((time / 240 : U32), (t0 / 240 : U32))), 11, 0.35, bpan, 1.0, False{},
    Cue.add((U32.is_eq(m0, 0) && U32.is_eq(mode, 1)), 14, 0.65, 0.0, 1.0, False{},
    Cue.add((attack && special && U32.is_eq((time % 3 : U32), 0)), 15, 0.40, pan, 1.0, False{},
    Cue.add((bfresh && U32.is_eq(state, 7)), 4, 0.98, bpan, 0.8, False{},
    Cue.add((bfresh && U32.is_eq(state, 5)), 5, 0.55, bpan, 1.0, False{},
    Cue.add((bfresh && Act.in(state, 1, 5)), 11, 0.30, bpan, 1.0, False{}, acc))))))))))))))

# Loop
# ----

# The live state: the game, the tick before it (the view lies between
# them), the clock at the last frame, the debt of a tick in
# thousandths, the clock the frame count began at and the count, the
# cues of the frame's ticks.
type Live is Data:
  Live{game: Game, prev: Game, stamp: Nat, debt: U32, begin: Nat, frames: U32, cues: List<&2, Cue>}

def Live.fresh(+stamp: Nat) -> Live:
  Live{Game.init(), Game.init(), stamp, 0, stamp, 0, Nil{}}

def Game.paused(+g: Game) -> Bool:
  Game{_, _, _, mode, _, _, _, _, _, _, _} = g
  U32.is_eq(mode, 4)

def Game.quit(esc: Bool, g: Game) -> Maybe<Game>:
  match esc:
    case True{}:
      None{}
    case False{}:
      Some{g}

# A key sets its bit; Esc or Close ends.
def Game.event(+e: Event, g: Game) -> Maybe<Game>:
  match e:
    case Key{code, down}:
      Game.quit(U32.is_eq(code, 27), Game.key(g, code, down))
    case Close{}:
      None{}
    case _:
      Some{g}

def Game.events(events: List<Event>, g: Game) -> Maybe<Game>:
  match events:
    case Nil{}:
      Some{g}
    case Con{e, rest}:
      Maybe.bind(&1, Game, Game, Game.event(e, g), g2 => Game.events(rest, g2))

# n ticks, the last two kept, their cues gathered.
def Live.steps(
  n: Nat, prev: Game, +g: Game, now: Nat, +debt: U32, begin: Nat, +frames: U32, cues: List<&2, Cue>
) -> Live:
  match n:
    case 0n:
      Live{g, prev, now, debt, begin, frames, cues}
    case 1n+k:
      +g2 = Game.step(g)
      Live.steps(k, g, g2, now, debt, begin, frames, Cue.list(g, g2, cues))

# The ticks a frame owes: 60 a second of the elapsed time (at most 100
# ms of it), the rest kept as debt.
def Live.time(
  +g: Game, prev: Game, +stamp: Nat, +debt: U32, +now: Nat, begin: Nat, +frames: U32,
  cues: List<&2, Cue>
) -> Live:
  +ms = U32.from_nat(Nat.sub(now, stamp))
  +total = (debt + Math.word((ms < 100 : U32), ms, 100) * 60 : U32)
  Live.steps(U32.to_nat((total / 1000 : U32)), prev, g, now, (total % 1000 : U32), begin,
    frames, cues)

def Live.after(
  m: Maybe<Game>, prev: Game, stamp: Nat, debt: U32, now: Nat, begin: Nat, frames: U32,
  cues: List<&2, Cue>
) -> Maybe<Live>:
  match m:
    case None{}:
      None{}
    case Some{g}:
      Some{Live.time(g, prev, stamp, debt, now, begin, frames, cues)}

def Live.view(+s: Live, used: Cells) -> Cells:
  Live{game, prev, _, debt, _, _, _} = s
  +u = (U32.to_f32(debt) / 1000.0 : F32)
  Scene.build(Game.lerp(prev, game, u), Game.clock(game, u), used)

def Play.title(+fps: U32) -> String:
  "MOON SEVER | Super Slash Boss 3D | " ++ U32.show(fps) ++ " FPS"

# The frames counted: past half a second (ms since the count began),
# the title shows their rate and a new count begins at now; the
# window, the count's start and the count.
def Play.pace.go(
  ready: Bool, window: Window, +ms: U32, +count: U32, now: Nat, begin: Nat
) -> IO(Window & Nat & U32):
  match ready:
    case False{}:
      IO.pure(Window & Nat & U32, (window, begin, count))
    case True{}:
      IO.bind(Window, Window & Nat & U32,
        Window.set_title(window, Play.title(((count * 1000 + ms / 2) / ms : U32))),
        w => IO.pure(Window & Nat & U32, (w, now, 0)))

def Play.pace(
  window: Window, +ms: U32, +count: U32, now: Nat, begin: Nat
) -> IO(Window & Nat & U32):
  Play.pace.go((ms >= 500 : U32), window, ms, count, now, begin)

# The frame's cues into the sound and the device fed (silent in a
# pause), then the next turn.
def Play.serve(
  window: Window, +live: Live, snd: Sound, +now: Nat, rest: Window -> Live -> Sound -> IO(Unit)
) -> IO(Unit):
  Live{game, prev, stamp, debt, begin, frames, cues} = live
  do IO<Unit>:
    snd2 : Sound <- Sound.serve(snd, cues, now, Game.paused(game))
    rest(window, Live{game, prev, stamp, debt, begin, frames, Nil{}}, snd2)

# The end closes the sound and the window.
def Play.go(
  window: Window, snd: Sound, +now: Nat, rest: Window -> Live -> Sound -> IO(Unit), next: Maybe<Live>
) -> IO(Unit):
  match next:
    case None{}:
      do IO<Unit>:
        Unit <- Sound.close(snd)
        Window.close(window)
    case Some{live}:
      Play.serve(window, live, snd, now, rest)

def Play.after(
  paced: Window & Nat & U32, m: Maybe<Game>, prev: Game, stamp: Nat, debt: U32, +now: Nat,
  cues: List<&2, Cue>, snd: Sound, rest: Window -> Live -> Sound -> IO(Unit)
) -> IO(Unit):
  (window, begin, frames) = paced
  Play.go(window, snd, now, rest, Live.after(m, prev, stamp, debt, now, begin, frames, cues))

# The title paced, the events into the game, then the ticks owed.
def Play.next(
  window: Window, events: List<Event>, game: Game, prev: Game, stamp: Nat, debt: U32,
  +begin: Nat, +frames: U32, +now: Nat, cues: List<&2, Cue>, snd: Sound,
  rest: Window -> Live -> Sound -> IO(Unit)
) -> IO(Unit):
  do IO<Unit>:
    paced : Window & Nat & U32 <- Play.pace(window, U32.from_nat(Nat.sub(now, begin)),
      (frames + 1 : U32), now, begin)
    Play.after(paced, Game.events(events, game), prev, stamp, debt, now, cues, snd, rest)

# The image shown and its scene are kept for the next frame's bang and
# build to drop.
def Play.turn(
  shown: Window & Image & List<Event>, cells: Cells, +s: Live, snd: Sound,
  rest: Window -> Live -> Sound -> (Image & Cells) -> IO(Unit)
) -> IO(Unit):
  (window, image, events) = shown
  Live{game, prev, stamp, debt, begin, frames, cues} = s
  do IO<Unit>:
    now : Nat <- IO.now()
    Play.next(window, events, game, prev, stamp, debt, begin, frames, now, cues, snd,
      w => l => sn => rest(w, l, sn, (image, cells)))

# The frame to the window, the next turn.
def Play.blit(
  drawn: Image & Cells, window: Window, s: Live, snd: Sound,
  rest: Window -> Live -> Sound -> (Image & Cells) -> IO(Unit)
) -> IO(Unit):
  (image, cells) = drawn
  do IO<Unit>:
    shown : Window & Image & List<Event> <- Window.frame(window, image)
    Play.turn(shown, cells, s, snd, rest)

# A turn: the scene (the last one dropped in its build), an IO seam (the
# bang must not follow the host's forks in one evaluation), the frame
# (the last one dropped in its bang).
@unsafe
def Play.loop(window: Window, +s: Live, snd: Sound, last: Image & Cells) -> IO(Unit):
  (old, used) = last
  do IO<Unit>:
    cells : Cells = Live.view(s, used)
    now : Nat <- IO.now()
    drawn : Image & Cells <- IO.pure(Image & Cells, Frame.show(cells, old))
    Play.blit(drawn, window, s, snd, w => s2 => snd2 => l => Play.loop(w, s2, snd2, l))

def Play.run() -> IO(Unit):
  do IO<Unit>:
    window : Window <- IO.try(Window, Window.open("Moon Sever", 1920, 1200))
    snd : Sound <- Sound.open()
    stamp : Nat <- IO.now()
    Play.loop(window, Live.fresh(stamp), snd, (Pix{0}, CNil{}))

# Probe
# -----

def Script.at(+t: U32, +a: U32, +b: U32, +m: U32) -> U32:
  Math.word(((t >= a) && (t < b) : U32), m, 0)

# The keys held at a tick of the script: L starts; a run right; J; a
# hop and an air J; D + J held into a side smash, charged and released;
# W + J; S + J; K; W + K; a run right; S + K; a guard; a hop, A held
# and an L tap (an air dodge left); hops with W + J, S + J, D + J and A
# + J; D + K, a dash; a walk off the edge, the fall and the respawn;
# then a jab, two sides, an up, a down and a side special at the boss
# on the left.
def Script.held(+t: U32) -> U32:
  (Script.at(t, 1, 3, 128) .|. Script.at(t, 60, 84, 8) .|. Script.at(t, 90, 92, 16)
    .|. Script.at(t, 120, 122, 64) .|. Script.at(t, 126, 128, 16)
    .|. Script.at(t, 180, 182, 8) .|. Script.at(t, 180, 230, 16)
    .|. Script.at(t, 260, 262, 17) .|. Script.at(t, 290, 292, 20)
    .|. Script.at(t, 330, 332, 32) .|. Script.at(t, 370, 372, 33)
    .|. Script.at(t, 340, 356, 8) .|. Script.at(t, 420, 422, 36)
    .|. Script.at(t, 480, 540, 128)
    .|. Script.at(t, 560, 562, 64) .|. Script.at(t, 566, 580, 2) .|. Script.at(t, 568, 570, 128)
    .|. Script.at(t, 620, 622, 64) .|. Script.at(t, 626, 628, 17)
    .|. Script.at(t, 660, 662, 64) .|. Script.at(t, 666, 668, 20)
    .|. Script.at(t, 700, 702, 64) .|. Script.at(t, 706, 708, 24)
    .|. Script.at(t, 740, 742, 64) .|. Script.at(t, 746, 748, 18)
    .|. Script.at(t, 800, 802, 40) .|. Script.at(t, 830, 880, 8)
    .|. Script.at(t, 900, 902, 16) .|. Script.at(t, 950, 952, 18) .|. Script.at(t, 1000, 1002, 18)
    .|. Script.at(t, 1050, 1052, 17) .|. Script.at(t, 1100, 1102, 20)
    .|. Script.at(t, 1150, 1152, 34) : U32)

# The script's rig: the hero has 9 lives from tick 10; the boss's
# vitality is 150 at tick 420 (enraged) and 3 at 900 (the next hit
# kills).
def Script.hp(+g: Game, +t: U32) -> Game:
  Game{time, held, taps, mode, hero, boss, flash, cloth, garb, lens, blast} = g
  Fighter{q, hv, yaw, damage, guard, jumps, action, hage, inv, stocks, grace, queued, charge} = hero
  Boss{p, v, face, hp, stun, strain, state, age, hold, mark, gait} = boss
  Game{time, held, taps, mode, Fighter{q, hv, yaw, damage, guard, jumps, action, hage, inv,
      Math.word(U32.is_eq(t, 10), 9, stocks), grace, queued, charge},
    Boss{p, v, face, Math.pick(U32.is_eq(t, 420), 150.0, Math.pick(U32.is_eq(t, 900), 3.0, hp)),
      stun, strain, state, age, hold, mark, gait}, flash, cloth, garb, lens, blast}

def Script.tick(+g: Game, +t: U32) -> Game:
  +h = Script.held(t)
  Game.step(Script.hp(Game.keys(g, h, (h .&. U32.not(Script.held(Sim.dec(t))) : U32)), t))

def Game.walk(n: Nat, +g: Game, +t: U32) -> Game:
  match n:
    case 0n:
      g
    case 1n+k:
      Game.walk(k, Script.tick(g, t), (t + 1 : U32))

# The probe's rig: SLASH_MODE puts the game in a mode (9: the fight
# with the parry cue up; else as it is).
def Probe.rig(+g: Game, +m: U32) -> Game:
  Game{time, held, taps, mode, hero, boss, flash, cloth, garb, lens, blast} = g
  Fighter{p, v, face, damage, guard, jumps, action, age, inv, stocks, grace, queued, charge} = hero
  Boss{q, bv, yaw, hp, stun, strain, state, bage, hold, mark, gait} = boss
  +cue = U32.is_eq(m, 9)
  Game{time, held, taps, Math.word((m > 4 : U32), mode, m),
    Fighter{p, v, face, damage, guard, jumps, Math.word(cue, 3, action), age, inv, stocks, grace,
      queued, charge},
    Boss{q, bv, yaw, hp, Math.word(cue, 5, stun), strain, state, bage, hold, mark, gait},
    Math.word(cue, 3, flash), cloth, garb, lens, blast}

# The measured frames: their count and the ms of the scene's build, the
# frame's bang, the image's drop, the scene's drop, the sim's tick, the
# sound's mix and the whole turn.
type Sums is Data:
  Sums{n: U32, build: U32, draw: U32, drop: U32, free: U32, tick: U32, mix: U32, whole: U32}


def Probe.ms(+a: Nat, +b: Nat) -> U32:
  U32.from_nat(Nat.sub(b, a))

def Sums.add(
  warm: Bool, +s: Sums, +b: U32, +d: U32, +p: U32, +f: U32, +k: U32, +m: U32, +w: U32
) -> Sums:
  match warm:
    case True{}:
      s
    case False{}:
      Sums{n, sb, sd, sp, sf, sk, sm, sw} = s
      Sums{(n + 1 : U32), (sb + b : U32), (sd + d : U32), (sp + p : U32),
        (sf + f : U32), (sk + k : U32), (sm + m : U32), (sw + w : U32)}

# The sums after a frame (the clocks after its scene and its bang),
# beside its image and its scene (the next bang and build drop them;
# their drops count 0).
def Sums.next(
  ti: Nat & Nat & Image & Cells, warm: Bool, +s: Sums, +t0: Nat, +t5: Nat, +t6: Nat, +t7: Nat
) -> Sums & Image & Cells:
  (+t1, t2, img, used) = ti
  (Sums.add(warm, s, Probe.ms(t0, t1), Probe.ms(t1, t2), 0, 0, Probe.ms(t5, t6),
    Probe.ms(t6, t7), Probe.ms(t0, t7)), img, used)

# Microseconds a frame.
def Probe.us(+sum: U32, +n: U32) -> String:
  U32.show((sum * 1000 / n : U32))

def Probe.report(+s: Sums) -> IO(Unit):
  Sums{n, build, draw, drop, free, tick, mix, whole} = s
  IO.print("frames " ++ U32.show(n) ++ " build " ++ Probe.us(build, n) ++ " draw "
    ++ Probe.us(draw, n) ++ " drop " ++ Probe.us(drop, n) ++ " free "
    ++ Probe.us(free, n) ++ " tick " ++ Probe.us(tick, n) ++ " mix " ++ Probe.us(mix, n)
    ++ " whole " ++ Probe.us(whole, n))

# The frame of a built scene: the bang (the last image dropped in it)
# timed; the image and the scene come back for the next frame to drop.
def Probe.frame(cells: Cells, old: Image) -> IO(Nat & Nat & Image & Cells):
  do IO<Nat & Nat & Image & Cells>:
    t1 : Nat <- IO.now()
    drawn : Image & Cells <- IO.pure(Image & Cells, Frame.show(cells, old))
    t2 : Nat <- IO.now()
    IO.pure(Nat & Nat & Image & Cells, (t1, t2, drawn))

# The state in a line: the tick, the mode, the hero (place, speed,
# action, damage, guard, lives, invulnerable ticks), the boss (place,
# vitality, stun).
def Probe.line(+g: Game) -> String:
  Game{time, _, _, mode, hero, boss, _, _, _, _, _} = g
  Fighter{p, v, _, damage, guard, _, action, age, inv, stocks, _, _, _} = hero
  Vec{x, y, _} = p
  Vec{vx, vy, _} = v
  Boss{q, _, _, hp, stun, _, state, bage, _, _, _} = boss
  Vec{bx, by, _} = q
  "t " ++ U32.show(time) ++ " mode " ++ U32.show(mode) ++ " hero " ++ F32.show(x) ++ " "
    ++ F32.show(y) ++ " v " ++ F32.show(vx) ++ " " ++ F32.show(vy) ++ " act " ++ U32.show(action)
    ++ " dmg " ++ F32.show(damage) ++ " guard " ++ F32.show(guard) ++ " lives "
    ++ U32.show(stocks) ++ " inv " ++ U32.show(inv) ++ " boss " ++ F32.show(bx) ++ " "
    ++ F32.show(by) ++ " hp " ++ F32.show(hp) ++ " stun " ++ U32.show(stun) ++ " st "
    ++ U32.show(state) ++ " age " ++ U32.show(bage)

def Probe.say(on: Bool, text: String) -> IO(Unit):
  match on:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      IO.print(text)

# The blocks the probe's sound owes: each block rendered is taken out
# of the sound (the one rendered last sits in it) onto the list, newest
# first.
def Probe.push(block: List<&2, F32>, acc: List<&2, List<&2, F32>>) -> List<&2, List<&2, F32>>:
  match block:
    case Nil{}:
      acc
    case Con{x, rest}:
      Con{Con{x, rest}, acc}

def Probe.render(
  n: Nat, s: Sound, acc: List<&2, List<&2, F32>>
) -> Sound & List<&2, List<&2, F32>>:
  match n:
    case 0n:
      Sound{dev, pcm, bank, voices, prev, block, queued, stamp} = s
      (Sound{dev, pcm, bank, voices, prev, Nil{}, queued, stamp}, Probe.push(block, acc))
    case 1n+k:
      Sound{dev, pcm, bank, voices, prev, block, queued, stamp} = s
      Probe.render(k, Mix.render(Sound{dev, pcm, bank, voices, prev, Nil{}, queued, stamp}),
        Probe.push(block, acc))

# A block as a line of its samples' bits.
def Probe.text(b: List<&2, F32>) -> String:
  match b:
    case Nil{}:
      "\n"
    case Con{x, rest}:
      U32.show(F32.bits(x)) ++ " " ++ Probe.text(rest)

def Probe.wrote(w: File & Result<&1, &1, U32 & String, Unit>) -> IO(Maybe<File>):
  (f, r) = w
  IO.pure(Maybe<File>, Some{f})

def Probe.put(b: List<&2, F32>, f: Maybe<File>) -> IO(Maybe<File>):
  match f:
    case None{}:
      IO.pure(Maybe<File>, None{})
    case Some{file}:
      do IO<Maybe<File>>:
        w : File & Result<&1, &1, U32 & String, Unit> <- File.write(file, Probe.text(b))
        Probe.wrote(w)

# The blocks (newest first) written oldest first.
def Probe.wav(blocks: List<&2, List<&2, F32>>, f: Maybe<File>) -> IO(Maybe<File>):
  match blocks:
    case Nil{}:
      IO.pure(Maybe<File>, f)
    case Con{b, rest}:
      do IO<Maybe<File>>:
        f2 : Maybe<File> <- Probe.wav(rest, f)
        Probe.put(b, f2)

def Probe.close(f: Maybe<File>) -> IO(Unit):
  match f:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{file}:
      File.close(file)

def Probe.mixed(
  b: Game, +cues: List<&2, Cue>, r: Sound & List<&2, List<&2, F32>>
) -> Game & Sound & List<&2, Cue> & List<&2, List<&2, F32>>:
  (snd, blocks) = r
  (b, snd, cues, blocks)

# A tick's cues into the sound and n blocks rendered: the game after,
# the sound, the cues, the blocks.
def Probe.mix(
  +a: Game, +g2: Game, snd: Sound, n: Nat
) -> Game & Sound & List<&2, Cue> & List<&2, List<&2, F32>>:
  +cues = Cue.list(a, g2, Nil{})
  Probe.mixed(g2, cues, Probe.render(n, Sound.cues(cues, snd), Nil{}))

def Probe.cues(cues: List<&2, Cue>, +t: U32) -> IO(Unit):
  match cues:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{Cue{kind, gain, pan, rate, _}, rest}:
      do IO<Unit>:
        Unit <- IO.print("cue t " ++ U32.show(t) ++ " kind " ++ U32.show(kind) ++ " gain "
          ++ F32.show(gain) ++ " pan " ++ F32.show(pan) ++ " rate " ++ F32.show(rate))
        Probe.cues(rest, t)

def Sound.told(s: Sound, on: Bool) -> IO(Sound):
  Sound{dev, pcm, bank, voices, prev, block, queued, stamp} = s
  do IO<Sound>:
    Unit <- Probe.say(on, "queue " ++ U32.show(queued) ++ " voices " ++ U32.show(Voices.count(voices)))
    IO.pure(Sound, Sound{dev, pcm, bank, voices, prev, block, queued, stamp})

# The device fed as in the game (no dump asked), its queue told every
# 60 ticks.
def Probe.serve(feed: Bool, s: Sound, +now: Nat, +t: U32) -> IO(Sound):
  match feed:
    case False{}:
      IO.pure(Sound, s)
    case True{}:
      do IO<Sound>:
        s2 : Sound <- Sound.serve(s, Nil{}, now, False{})
        Sound.told(s2, U32.is_eq((t % 60 : U32), 0))

# The summary every 60 ticks, the state on a dodge's first tick, on
# the boss's first tick of a state or a stun and on the hero's first
# hurt tick; the game answered.
def Probe.watch(+g: Game, +t: U32) -> IO(Game):
  Game{_, _, _, mode, hero, boss, _, _, _, _, _} = g
  Fighter{_, _, _, _, _, _, action, age, _, _, _, _, _} = hero
  Boss{_, _, _, _, stun, _, state, bage, _, _, _} = boss
  do IO<Game>:
    Unit <- Probe.say(U32.is_eq((t % 60 : U32), 0), Probe.line(g))
    Unit <- Probe.say((U32.is_eq(action, 6) && U32.is_eq(age, 28)), "dodge " ++ Probe.line(g))
    Unit <- Probe.say((U32.is_eq(mode, 1) && U32.is_eq(bage, 0) && ((state > 0 : U32)
      || (stun > 0 : U32))), "boss " ++ Probe.line(g))
    Unit <- Probe.say((U32.is_eq(action, 4) && U32.is_eq(age, 23)), "hurt " ++ Probe.line(g))
    IO.pure(Game, g)

# N frames of the scripted game: the view between the last two ticks,
# the frame, the drops, the tick and the mix (the 800 frames a tick
# owes, in blocks of 512, the rest carried as due), each timed; the
# first 8 warm up. A turn opens with the last tick's cues and blocks
# (the blocks to the SLASH_WAV file) and its state watched.
def Probe.loop(
  left: Nat, gs: Game & Sound & List<&2, Cue> & List<&2, List<&2, F32>>, +prev: Game, +t: U32,
  si: Sums & Image & Cells, +seen: Nat, +rig: U32, +due: U32, file: Maybe<File>, +feed: Bool
) -> IO(Unit):
  match left:
    case 0n:
      (g, snd, cues, blocks) = gs
      (s, img, used) = si
      do IO<Unit>:
        f2 : Maybe<File> <- Probe.wav(blocks, file)
        Unit <- Probe.cues(cues, Sim.dec(t))
        g1 : Game <- Probe.watch(g, Sim.dec(t))
        Unit <- Probe.close(f2)
        Unit <- Sound.close(snd)
        Probe.report(s)
    case 1n+k:
      (g, snd, cues, blocks) = gs
      (s, img, used) = si
      +game = g
      do IO<Unit>:
        f2 : Maybe<File> <- Probe.wav(blocks, file)
        Unit <- Probe.cues(cues, Sim.dec(t))
        g1 : Game <- Probe.watch(game, Sim.dec(t))
        t8 : Nat <- IO.now()
        snd2 : Sound <- Probe.serve(feed, snd, t8, Sim.dec(t))
        t0 : Nat <- IO.now()
        cells : Cells = Scene.build(Probe.rig(Game.lerp(prev, game, 0.5), rig), Game.clock(game, 0.5),
          used)
        ti : Nat & Nat & Image & Cells <- Probe.frame(cells, img)
        t5 : Nat <- IO.now()
        g2 : Game = Script.tick(game, t)
        t6 : Nat <- IO.now()
        gs2 : Game & Sound & List<&2, Cue> & List<&2, List<&2, F32>> <-
          IO.pure(Game & Sound & List<&2, Cue> & List<&2, List<&2, F32>>,
            Probe.mix(game, g2, snd2, U32.to_nat(Math.word(feed, 0, ((due + 800) / 512 : U32)))))
        t7 : Nat <- IO.now()
        Probe.loop(k, gs2, game, (t + 1 : U32), Sums.next(ti, Nat.is_lt(seen, 8n), s, t0, t5, t6, t7),
          1n+seen, rig, ((due + 800) % 512 : U32), f2, feed)

# A frame as lines: Q opens a node, a number is a Pix.
def Dump.tree(img: Image) -> IO(Unit):
  match img:
    case Pix{c}:
      IO.print(U32.show(c))
    case Qua{tl, tr, bl, br}:
      do IO<Unit>:
        Unit <- IO.print("Q")
        Unit <- Dump.tree(tl)
        Unit <- Dump.tree(tr)
        Unit <- Dump.tree(bl)
        Dump.tree(br)

def Frame.only(drawn: Image & Cells) -> Image:
  (img, _) = drawn
  img

def Env.u32(m: Maybe<&2, U32>, default: U32) -> U32:
  match m:
    case None{}:
      default
    case Some{v}:
      v

def Env.num(r: Result<&1, &1, U32 & String, String>, +default: U32) -> U32:
  match r:
    case Fail{_}:
      default
    case Done{text}:
      Env.u32(U32.read(text), default)

def Probe.scene(+g: Game) -> Cells:
  Scene.build(g, Game.clock(g, 1.0), CNil{})

def Probe.dump(dump: Result<&1, &1, U32 & String, String>, +rig: U32) -> IO(Unit):
  match dump:
    case Fail{_}:
      IO.pure(Unit, Unit{})
    case Done{text}:
      do IO<Unit>:
        cells : Cells = Probe.scene(Probe.rig(Game.walk(U32.to_nat(Env.u32(U32.read(text), 1)),
          Game.init(), 0), rig))
        now : Nat <- IO.now()
        Dump.tree(Frame.only(Frame.show(cells, Pix{0})))

def Probe.rest(n: Nat, +rig: U32, snd: Sound, file: Maybe<File>, feed: Bool) -> IO(Unit):
  do IO<Unit>:
    Unit <- Probe.loop(n, (Game.init(), snd, Nil{}, Nil{}), Game.init(), 0,
      (Sums{0, 0, 0, 0, 0, 0, 0, 0}, Pix{0}, CNil{}), 0n, rig, 0, file, feed)
    dump : Result<&1, &1, U32 & String, String> <- IO.get_env("SLASH_DUMP")
    Probe.dump(dump, rig)

# n looping voices over the synthesized clips (SLASH_VOICES loads the
# mixer).
def Sound.fill(+n: Nat, s: Sound) -> Sound:
  match n:
    case 0n:
      s
    case 1n+k:
      Sound.fill(k, Sound.play(s, Cue{(U32.from_nat(k) % 13 : U32), 0.1, 0.0, 1.0, True{}}))

def Env.none(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Fail{_}:
      True{}
    case Done{_}:
      False{}

def Probe.file.got(r: Result<&1, &1, U32 & String, File>) -> Maybe<File>:
  match r:
    case Fail{_}:
      None{}
    case Done{f}:
      Some{f}

# The SLASH_WAV file opened to write.
def Probe.file(r: Result<&1, &1, U32 & String, String>) -> IO(Maybe<File>):
  match r:
    case Fail{_}:
      IO.pure(Maybe<File>, None{})
    case Done{path}:
      do IO<Maybe<File>>:
        f : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
        IO.pure(Maybe<File>, Probe.file.got(f))

def Probe.run(text: String) -> IO(Unit):
  do IO<Unit>:
    mode : Result<&1, &1, U32 & String, String> <- IO.get_env("SLASH_MODE")
    voices : Result<&1, &1, U32 & String, String> <- IO.get_env("SLASH_VOICES")
    wav : Result<&1, &1, U32 & String, String> <- IO.get_env("SLASH_WAV")
    feed : Result<&1, &1, U32 & String, String> <- IO.get_env("SLASH_WAV")
    snd : Sound <- Sound.open()
    file : Maybe<File> <- Probe.file(wav)
    Probe.rest(U32.to_nat(Env.u32(U32.read(text), 600)), Env.num(mode, 99),
      Sound.fill(U32.to_nat(Env.num(voices, 0)), snd), file, Env.none(feed))

def Main.mode(probe: Result<&1, &1, U32 & String, String>) -> IO(Unit):
  match probe:
    case Fail{_}:
      Play.run()
    case Done{text}:
      Probe.run(text)

def main() -> IO(Unit):
  do IO<Unit>:
    probe : Result<&1, &1, U32 & String, String> <- IO.get_env("SLASH_PROBE")
    Main.mode(probe)
