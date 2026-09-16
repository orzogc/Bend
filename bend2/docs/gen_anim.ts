#!/usr/bin/env node
// The README's two page animations, media/hero.gif and media/parallel.gif.
//
// hero.gif is the landing page's hero: the word Bend, the purple block
// blinking after it, and the one line under it. parallel.gif is the
// landing page's pow2 canvas: the call splits in two, in four, ... until
// one task sits on each of 64 x 64 cores; every core works its task; the
// results fold back pairwise; the view zooms on the one cell that holds
// the answer.
//
// Both are drawn on a TRANSPARENT canvas, in the palette of the chart
// gifs, so they read on the light and on the dark GitHub. A gif has
// 1-bit alpha, so ffmpeg disposes every frame to the background and
// nothing of the frame before shows through.
//
// It needs node >= 22.18, the canvas package, ffmpeg and Menlo, which
// this Mac lacks: render on cluster-9d, where ~/film has all four.
//
//   tar cf - bend2/docs/gen_anim.ts | ssh -J cluster cluster-9d 'cd film && tar xf -'
//   ssh -J cluster cluster-9d 'cd film && \
//     PATH=/usr/local/node/bin:$PATH:$HOME/film node bend2/docs/gen_anim.ts'
//   scp -o ProxyJump=cluster 'cluster-9d:film/media/{hero,parallel}.gif' media/

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { createCanvas } from "canvas";

// Constants
// =========

const ROOT = path.join(import.meta.dirname, "..", "..");
const MONO = "Menlo, monospace";
const INK = "#87847d";
const DIM = "#a5a29a";
const PURPLE = "#8b83b5";
const FPS = 12.5;

// Lib
// ===

function clamp(x: number): number {
  return x < 0 ? 0 : x > 1 ? 1 : x;
}

function ease(x: number): number {
  const u = clamp(x);
  return u * u * (3 - 2 * u);
}

function lerp(a: number, b: number, x: number): number {
  return a + (b - a) * x;
}

function mix(a: string, b: string, f: number): string {
  const pick = (h: string, i: number): number =>
    parseInt(h.slice(1 + 2 * i, 3 + 2 * i), 16);
  const one = (i: number): string =>
    String(Math.round(lerp(pick(a, i), pick(b, i), clamp(f))));
  return "rgb(" + one(0) + "," + one(1) + "," + one(2) + ")";
}

// the frames go to ffmpeg through a concat list, which keeps every
// duration, so a frame that holds is one frame with a long delay
function gif(name: string, cv: { width: number; height: number;
  toBuffer: (t: "image/png") => Buffer }, draw: (t: number) => void,
  shots: [number, number][]): void {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), name + "-"));
  const file = (i: number): string =>
    path.join(dir, "f" + String(i).padStart(4, "0") + ".png");
  let list = "ffconcat version 1.0\n";
  shots.forEach(([t, d], i): void => {
    draw(t);
    fs.writeFileSync(file(i), cv.toBuffer("image/png"));
    list += "file '" + file(i) + "'\nduration " + String(d) + "\n";
  });
  list += "file '" + file(shots.length - 1) + "'\n";
  fs.writeFileSync(path.join(dir, "list.txt"), list);
  const out = path.join(ROOT, "media", name + ".gif");
  const got = child.spawnSync("ffmpeg", ["-y", "-loglevel", "error", "-f",
    "concat", "-safe", "0", "-i", path.join(dir, "list.txt"), "-vf",
    "split[a][b];[a]palettegen=max_colors=63:reserve_transparent=1[p];"
    + "[b][p]paletteuse=dither=none:alpha_threshold=128",
    "-fps_mode", "vfr", "-loop", "0", out], { stdio: "inherit" });
  if (got.status !== 0) {
    throw new Error("ffmpeg failed on " + name);
  }
  fs.rmSync(dir, { recursive: true });
  process.stdout.write("wrote " + out + ": " + String(shots.length)
    + " frames, " + String(fs.statSync(out).size) + " bytes\n");
}

// Hero
// ====

// Bend, the block blinking after it, and the line under it: two frames,
// the block on and off, as the page blinks it every 1.1 s
function hero(): void {
  const W = 1280;
  const H = 300;
  const TITLE = 104;
  const SUB = 26;
  const LINE: [string, boolean][] = [["a ", false], ["fast", true],
    [" language that ", false], ["blocks AI mistakes", true],
    [" via ", false], ["proof", true]];
  const cv = createCanvas(W, H);
  const cx = cv.getContext("2d");
  const font = (size: number, bold: boolean): string =>
    (bold ? "bold " : "") + String(size) + "px " + MONO;
  function draw(t: number): void {
    cx.clearRect(0, 0, W, H);
    cx.textBaseline = "alphabetic";
    cx.textAlign = "left";
    cx.font = font(TITLE, true);
    const bw = TITLE * 0.5;
    const tw = cx.measureText("Bend").width + TITLE * 0.12 + bw;
    const tx = (W - tw) / 2;
    const ty = H * 0.46;
    cx.fillStyle = INK;
    cx.fillText("Bend", tx, ty);
    if (t < 0.55) {
      cx.fillStyle = PURPLE;
      cx.fillRect(tx + tw - bw, ty - TITLE * 0.79, bw, TITLE * 0.9);
    }
    let w = 0;
    for (const [s, bold] of LINE) {
      cx.font = font(SUB, bold);
      w += cx.measureText(s).width;
    }
    let x = (W - w) / 2;
    for (const [s, bold] of LINE) {
      cx.font = font(SUB, bold);
      cx.fillStyle = bold ? INK : DIM;
      cx.fillText(s, x, H * 0.82);
      x += cx.measureText(s).width;
    }
  }
  gif("hero", cv, draw, [[0, 0.55], [0.6, 0.55]]);
}

// Parallel
// ========

// pow2(20) splits in two, in four, ..., one task per core; each core
// works; the results fold back pairwise into the top-left cell, which
// the view then zooms on. The purple ramp is cold to hot: both ends
// read on white and on near-black.
function parallel(): void {
  const W = 960;
  const N = 64;
  const LEVELS = 12;
  const D0 = 0.9;
  const HOLD1 = 0.5;
  const ELEN = 0.9;
  const ESPREAD = 1.1;
  const ZLEN = 1.2;
  const TILES = ["#b0aac4", "#a49dbe", "#988fb8", "#8b83b5", "#7d75a4",
    "#6e6694", "#5e5787"];
  const split_dur = (k: number): number => 0.75 * Math.pow(0.82, k);
  const fold_dur = (j: number): number => 0.4 * Math.pow(0.85, j);
  const rung = (t: number): string => {
    const i = Math.min(Math.floor(t), TILES.length - 2);
    return mix(TILES[i], TILES[i + 1], t - i);
  };
  const HEAT: string[] = [];
  for (let i = 0; i <= 16; i++) {
    HEAT.push(rung(4 * i / 16));
  }
  const dims = (k: number): [number, number] =>
    [1 << Math.ceil(k / 2), 1 << Math.floor(k / 2)];
  const rnd = (i: number): number => {
    const s = Math.sin(i * 12.9898) * 43758.5453;
    return s - Math.floor(s);
  };
  const phase = (c: number, r: number): number =>
    rnd(c * 7919 + r * 104729) * ESPREAD;
  let split_end = D0;
  for (let k = 0; k < LEVELS; k++) {
    split_end += split_dur(k);
  }
  const E0 = split_end + HOLD1;
  const R0 = E0 + ELEN + ESPREAD + 0.5;
  let fold_end = R0;
  for (let j = 0; j < LEVELS; j++) {
    fold_end += fold_dur(j);
  }
  const Z0 = fold_end + 0.4;
  const Z1 = Z0 + ZLEN;
  const fold_at = (u: number): number => {
    let j = 0;
    let t = R0;
    while (j < LEVELS && u >= t + fold_dur(j)) {
      t += fold_dur(j);
      j++;
    }
    return j < LEVELS ? j + clamp((u - t) / fold_dur(j)) : LEVELS;
  };
  const cv = createCanvas(W, W);
  const cx = cv.getContext("2d");
  function cell(x: number, y: number, w: number, h: number,
    fill: string): void {
    const g = Math.min(Math.max(Math.min(w, h) * 0.1, 1), 6);
    cx.fillStyle = fill;
    cx.fillRect(x + g / 2, y + g / 2, w - g, h - g);
  }
  function label(s: string, x: number, y: number, w: number, h: number,
    ink: string): void {
    const fs = Math.min(Math.min(w, h) * 0.17, 44);
    if (fs < 7) {
      return;
    }
    cx.font = "bold " + String(fs) + "px " + MONO;
    if (cx.measureText(s).width > w * 0.9) {
      return;
    }
    cx.fillStyle = ink;
    cx.textAlign = "center";
    cx.fillText(s, x + w / 2, y + h / 2 + fs * 0.36);
  }
  // the k-th generation of tasks, m of the way out of its parent's seat.
  // A gif has 1-bit alpha, so nothing here fades. While the children
  // still overlap their parent, the parent's label is the one that
  // shows; once they are apart, each child names itself
  function slots(k: number, m: number): void {
    const [cols, rows] = dims(k);
    const w = W / cols;
    const h = W / rows;
    const [pc, pr] = k > 0 ? dims(k - 1) : [1, 1];
    const at = (c: number, r: number): [number, number] => [
      lerp((Math.floor(c * pc / cols) + 0.5) * (W / pc), (c + 0.5) * w, m)
        - w / 2,
      lerp((Math.floor(r * pr / rows) + 0.5) * (W / pr), (r + 0.5) * h, m)
        - h / 2];
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        const [x, y] = at(c, r);
        cell(x, y, w, h, TILES[0]);
      }
    }
    const out = m >= 0.55;
    const name = "pow2(" + String(20 - (out ? k : k - 1)) + ")";
    for (let r = 0; r < (out ? rows : pr); r++) {
      for (let c = 0; c < (out ? cols : pc); c++) {
        const [x, y] = out ? at(c, r) : [c * (W / pc), r * (W / pr)];
        label(name, x, y, out ? w : W / pc, out ? h : W / pr, "#4a4463");
      }
    }
  }
  function draw(u: number): void {
    const cs = W / N;
    cx.clearRect(0, 0, W, W);
    if (u < E0) {
      let k = 0;
      let s = D0;
      while (k < LEVELS && u >= s + split_dur(k)) {
        s += split_dur(k);
        k++;
      }
      const d = split_dur(k);
      const cut = Math.min(0.5, d * 0.7);
      const p = k < LEVELS ? ease((u - (s + d - cut)) / cut) : 0;
      if (p > 0) {
        slots(k + 1, p);
      } else {
        slots(k, 1);
      }
    } else if (u < R0) {
      for (let r = 0; r < N; r++) {
        for (let c = 0; c < N; c++) {
          const j = clamp((u - E0 - phase(c, r)) / ELEN);
          cell(c * cs, r * cs, cs, cs, HEAT[Math.round(j * 16)]);
        }
      }
    } else if (u < Z0) {
      const f = fold_at(u);
      const j = Math.floor(f);
      const m = ease(f - j);
      const k = LEVELS - j;
      const [w, h] = dims(k);
      const vert = k % 2 === 1;
      const fill = rung(4 + 2 * f / LEVELS);
      for (let r = 0; r < h; r++) {
        for (let c = 0; c < w; c++) {
          cell((vert ? lerp(c, c / 2, m) : c) * cs,
            (vert ? r : lerp(r, r / 2, m)) * cs, cs, cs, fill);
        }
      }
    } else {
      const zs = cs * Math.pow(N, ease((u - Z0) / ZLEN));
      cell(0, 0, zs, zs, TILES[6]);
      if (u > Z1 - 0.1) {
        label("1048576", 0, 0, zs, zs, "#f2eee7");
      }
    }
  }
  const shots: [number, number][] = [];
  const end = Z1 + 0.9;
  for (let i = 0; i * (1 / FPS) < end; i++) {
    shots.push([i / FPS, 1 / FPS]);
  }
  shots[shots.length - 1][1] = 1.8;
  gif("parallel", cv, draw, shots);
}

// Main
// ====

hero();
parallel();
