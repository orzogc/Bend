#!/usr/bin/env bun
// The live demo, the way the page runs it. The page's button calls the
// lab's check, builds a Game on the checked book, and reads the law's own
// flags; when any step throws, the button does nothing visible and the
// page says nothing, so every step is a check here.
//
// Checks: the lab builds for the browser; ALL.bend checks, with no hole
// and nothing unsafe; the opening board replays at (8, 5), unwon; the map
// is 12 x 8; the law's reading of the drawn board finds the one flag the
// page draws; the front end's contract holds; and the flag law still
// reads the board itself, since a law over a def of main.bend is a law
// the AI can make true by editing that def.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

import * as lib from "./_lib";

// Constants
// =========

const TMP = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "bend-lab-")));
const OUT = path.join(TMP, "lab.mjs");
const GAME = path.join(lib.ROOT, "demos", "app_win_is_bug_2d");

// Gate
// ====

const fails: string[] = [];
let total = 0;

function check(what: string, ok: boolean): void {
  total += 1;
  if (!ok) {
    fails.push(what);
  }
}

try {
  const got = await lib.exec(process.execPath, [path.join(lib.ROOT, "front", "build.ts"),
    path.join(lib.ROOT, "front", "lab.ts"), OUT, "esm"], undefined, 120_000);
  check("the lab builds for the browser", got.code === 0);
  const lab = await import(OUT);
  const rep = await lab.check("ALL.bend");
  check("the demo checks: " + String(rep.text).split("\n")[0], rep.ok === true);
  const game = new lab.Game(rep.book);
  const st = game.replay([]);
  check("the opening board is (8, 5), unwon",
    st.x === 8 && st.y === 5 && st.won === false);
  const w = game.nat("map_w");
  const h = game.nat("map_h");
  check("the map is 12 x 8", w === 12 && h === 8);
  check("the law's reading of the board finds the one flag",
    game.flags(w, h).filter(Boolean).length === 1);
  check("the front end's contract holds", lab.api_check(game) === null);
  const laws = fs.readFileSync(path.join(GAME, "LAWS.bend"), "utf8");
  check("the flag law reads the board, not a def the AI owns",
    laws.includes("at_flag(board) == False{}")
    && !laws.includes("Game.at_flag") && laws.includes("def flag_at"));
} catch (e) {
  check(String((e as Error)?.message ?? e), false);
} finally {
  fs.rmSync(TMP, { recursive: true, force: true });
}

if (!lib.GATE) {
  for (const f of fails) {
    console.log("FAIL " + f);
  }
}
lib.verdict(total - fails.length, total);
