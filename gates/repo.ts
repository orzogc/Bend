#!/usr/bin/env bun
// The shape of the repo: every tracked file must match one allow line,
// and a textual file must stay under its ttok cap (a binary under its
// byte cap). Anything else in the tree is a failure.

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";

import * as lib from "./_lib";

// Types
// =====

type Rule = { at: RegExp; cap: number; bytes: boolean };

// Constants
// =========

const RULES: Rule[] = [];

// Allow
// =====

function allow(at: string | RegExp, cap: number, bytes = false): void {
  RULES.push({ at: typeof at === "string" ? new RegExp("^" + at
    .replace(/[.]/g, "\\.") + "$") : at, cap, bytes });
}

allow(".gitattributes", 200);
allow("AGENTS.md", 2000);
allow("README.md", 2500);
allow("bend2/base.bend", 20000);
allow("bend2/bend.lean", 400000);
allow("bend2/bend.ts", 40000);
allow("bend2/comp.ts", 60000);
allow("bend2/main.ts", 10000);
allow(/^bend2\/effs\/[a-z_]+\.(c|js)$/, 4000);
allow(/^bend2\/pack\/(\.gitignore|package\.json|tsconfig\.json|bun\.lock)$/, 1000);
allow(/^bend2\/docs\/(BendRT|BendTT)\/(main\.typ|refs\.bib)$/, 60000);
allow("bend2/docs/bend.sublime-syntax", 1000);
allow("bend2/docs/gen_charts.ts", 4000);
allow("bend2/docs/gen_pins.ts", 4000);
allow(/^bend2\/docs\/intro\/[a-z.]+$/, 20000);
allow(/^bench\/checker\/[a-z]+_[0-9]+\/main\.(bend|agda|lean|thy|v)$/, 3000000);
allow(/^bench\/checker\/_pin_\/[a-z0-9_]+\.txt$/, 2000);
allow(/^bench\/runtime\/[a-z]+\/main\.(bend|c|lean|ts)$/, 8000);
allow(/^bench\/runtime\/_pin_\/[a-z0-9_]+\.txt$/, 2000);
allow(/^demos\/[a-z0-9_]+\/[A-Za-z0-9_]+\.bend$/, 30000);
allow(/^demos\/[a-z0-9_]+\/[A-Za-z_]+\.(c|sh|md)$/, 4000);
allow(/^demos\/[a-z0-9_]+\/web\/(index\.html|main\.js|bunfig\.toml)$/, 4000);
allow("guide/GUIDE.md", 12000);
allow("front/index.html", 12000);
allow("front/lab.ts", 12000);
allow("front/lab.md", 4000);
allow("front/pkg.html", 4000);
allow("front/hub.ts", 2500);
allow(/^front\/(Caddyfile|bendhub\.service)$/, 400);
allow(/^front\/(build|shim)\.ts$/, 1500);
allow("front/lab.js", 400000, true);
allow(/^paper\/(BendRT|BendTT)\.pdf$/, 400000, true);
allow(/^media\/intro\.(gif|mp4)$/, 25000000, true);
allow(/^media\/[a-z_]+\.svg$/, 40000, true);
allow(/^media\/slash_bros_3d\/[a-z_]+\.(wav|mp3)$/, 400000, true);
allow(/^gates\/(_lib|_run|perf|repo|test)\.ts$/, 6000);
allow(/^tests\/[a-z]+\/[a-z0-9_]+\.bend$/, 16000);
allow(/^tests\/[a-z]+\/[a-z0-9_]+\.(c|js)$/, 8000);

// Gate
// ====

function ttok(file: string): number {
  const got = child.spawnSync("ttok", [], { input: fs.readFileSync(file) });
  return Number(got.stdout.toString().trim());
}

function gate(): string[] {
  const fails: string[] = [];
  const files = child.execFileSync("git", ["ls-files"], { cwd: lib.ROOT,
    encoding: "utf8" }).trim().split("\n");
  for (const file of files) {
    const rule = RULES.find((r) => r.at.test(file));
    if (rule === undefined) {
      fails.push(file + ": not in the allow list");
      continue;
    }
    const full = path.join(lib.ROOT, file);
    const size = fs.statSync(full).size;
    const n = rule.bytes || size <= rule.cap ? size : ttok(full);
    if (n > rule.cap) {
      fails.push(file + ": " + String(n) + " > " + String(rule.cap)
        + (rule.bytes ? " bytes" : " ttok"));
    }
  }
  return fails;
}

// Main
// ====

if (import.meta.main) {
  const fails = gate();
  if (!lib.GATE) {
    for (const f of fails) {
      console.log("FAIL " + f);
    }
  }
  lib.verdict(RULES.length - Math.min(RULES.length, fails.length),
    RULES.length);
}
