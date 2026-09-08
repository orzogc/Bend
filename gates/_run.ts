#!/usr/bin/env bun
// Runs the three gates with --gate and prints their verdicts.

import * as child from "node:child_process";
import * as path from "node:path";

let ok = true;
for (const gate of ["repo", "test", "perf"]) {
  const got = child.spawnSync(process.execPath, [path.join(import.meta.dirname,
    gate + ".ts"), "--gate"], { encoding: "utf8" });
  console.log(gate.padEnd(5) + " " + (got.stdout + got.stderr).trim()
    .split("\n").pop());
  ok = ok && got.status === 0;
}
process.exit(ok ? 0 : 1);
