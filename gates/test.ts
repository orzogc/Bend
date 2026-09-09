#!/usr/bin/env bun
// Runs every test under tests/ on the cluster. The tests split into one
// shard per live mini; each shard is an aggregator that imports its tests,
// sent to its mini, which checks and runs every module through `bend main.bend
// --checkup -o main.js -o main` (the production build: clang -O3, Metal), runs
// one program untimed (the first launch compiles the shard's Metal shader,
// which the node then caches by source) and then runs each program once
// natively and once under bun, each under a 5 s alarm. A test passes when
// its check, its interpreted run, its JS run and its C run all print its
// `#|` lines; a module the combined book refuses (a name its own file
// binds and Base's sugar also names) is checked and interpreted only.

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";

import * as lib from "./_lib";

// Types
// =====

type Test = {
  name: string;
  src: string;
  want: string;
  main: boolean;
  lanes: string[];
};

type Got = Record<string, string>;

type Fail = { name: string; probe: string; want: string; got: string };

// Constants
// =========

const TESTS = path.join(lib.ROOT, "tests");

const MARK = "@@B4";

const LEFT = "Left out of the binary:\n";

const BUN = lib.BUN;

// Test
// ====

function test_read(dir: string, file: string): Test {
  const src = fs.readFileSync(path.join(TESTS, dir, file), "utf8");
  const want = src.split("\n").filter((l) => l.startsWith("#|"))
    .map((l) => l.slice(2)).join("\n");
  const effs = [...src.matchAll(/^\s*import "\.\/[a-z0-9_]+\.(c|js)"$/gm)]
    .map((m) => m[1]);
  const lanes = ["js", "c"].filter((l) =>
    effs.length === 0 || effs.includes(l));
  return { name: dir + "_" + path.basename(file, ".bend"), src,
    want: tidy(want), main: /^(def|law) main(\(|:)/m.test(src), lanes };
}

function tidy(text: string): string {
  return text.replace(/[ \t]+$/gm, "").trim();
}

function test_path(t: Test): string {
  return t.name.replace("_", "/") + ".bend";
}

function test_probes(t: Test, got: Got): string[] {
  if (!t.main || t.want.startsWith("Error:")) {
    return ["check"];
  }
  return ["check", "interp", ...("left" in got ? [] : t.lanes)];
}

function test_judge(t: Test, got: Got): Fail[] {
  const fails: Fail[] = [];
  for (const probe of test_probes(t, got)) {
    const seen = got[probe === "interp" ? "check" : probe]
      ?? "(no answer from the node)";
    const ok = probe === "check" && t.main && !t.want.startsWith("Error:")
      ? !seen.startsWith("Error:") : seen === t.want;
    if (!ok) {
      fails.push({ name: t.name, probe, want: t.want, got: seen });
    }
  }
  return fails;
}

// Shard
// =====

function shard_split(tests: Test[], count: number): Test[][] {
  const shards: Test[][] = Array.from({ length: count }, () => []);
  const sizes = shards.map(() => 0);
  for (const t of [...tests].sort((a, b) => b.src.length - a.src.length)) {
    const at = sizes.indexOf(Math.min(...sizes));
    shards[at].push(t);
    sizes[at] += t.src.length + 2000;
  }
  return shards.filter((s) => s.length > 0);
}

function shard_pack(shard: Test[]): Buffer {
  const dir = fs.mkdtempSync("/tmp/bend-shard-");
  fs.cpSync(path.join(lib.ROOT, "bend2"), path.join(dir, "bend2"),
    { recursive: true, filter: (p) =>
      !p.includes("/pack") && !p.includes("/docs") });
  for (const sub of fs.readdirSync(TESTS)) {
    fs.mkdirSync(path.join(dir, "tests", sub), { recursive: true });
    for (const f of fs.readdirSync(path.join(TESTS, sub))) {
      if (!f.endsWith(".bend")) {
        fs.copyFileSync(path.join(TESTS, sub, f),
          path.join(dir, "tests", sub, f));
      }
    }
  }
  for (const t of shard) {
    fs.writeFileSync(path.join(dir, "tests", test_path(t)), t.src);
  }
  fs.writeFileSync(path.join(dir, "main.bend"), shard.map((t) =>
    "import ./tests/" + test_path(t) + " as " + t.name).join("\n") + "\n");
  const tar = child.spawnSync("tar", ["-czf", "-", "-C", dir, "."],
    { maxBuffer: 1 << 28 });
  fs.rmSync(dir, { recursive: true, force: true });
  return tar.stdout;
}

function shard_script(shard: Test[], tag: number): string {
  const runs = shard.filter((t) => t.main && t.lanes.length > 0
    && !t.want.startsWith("Error:")).map((t) => t.name);
  const probe = (kind: string, cmd: string): string =>
    `echo "${MARK} ${kind} $m"; perl -e 'alarm 5; exec @ARGV' ${cmd} $m 2>&1;`
    + ` echo "${MARK} exit $?";`;
  return `export BUN_JSC_maxPerThreadStackUsage=33554432;`
    + ` d=$HOME/bend-test/${tag}; rm -rf $d; mkdir -p $d; cd $d; tar -xzf -;`
    + ` echo "${MARK} checkup"; ${BUN} bend2/main.ts main.bend --checkup`
    + ` -o main.js -o main 2>&1; echo "${MARK} built $?";`
    + ` perl -e 'alarm 60; exec @ARGV' ./main ${runs[0] ?? ""} >/dev/null 2>&1;`
    + ` for m in ${runs.join(" ")}; do ${probe("c", "./main")}`
    + ` ${probe("js", BUN + " main.js")} done; cd; rm -rf $d`;
}

function shard_parse(shard: Test[], out: string): Map<string, Got> {
  const gots = new Map<string, Got>(shard.map((t) => [t.name, {}]));
  const parts = out.split(new RegExp("^" + MARK + " ", "m")).slice(1);
  let last: [Got, string] | null = null;
  for (const part of parts) {
    const nl = part.indexOf("\n");
    const head = part.slice(0, nl).trim().split(" ");
    const body = part.slice(nl + 1);
    if (head[0] === "checkup") {
      const secs = body.split(/^--- \.\/tests\/([a-z0-9_/]+)\.bend ---\n/m);
      for (let i = 1; i + 1 < secs.length; i += 2) {
        const got = gots.get(secs[i].replace("/", "_"));
        const at = secs[i + 1].indexOf(LEFT);
        if (got !== undefined) {
          got.check = tidy(at < 0 ? secs[i + 1] : secs[i + 1].slice(0, at));
          if (at >= 0) {
            got.left = tidy(secs[i + 1].slice(at + LEFT.length));
          }
        }
      }
    } else if (head[0] === "c" || head[0] === "js") {
      const got = gots.get(head[1]);
      last = got === undefined ? null : [got, head[0]];
      if (got !== undefined) {
        got[head[0]] = tidy(body);
      }
    } else if (head[0] === "exit" && last !== null && head[1] !== "0") {
      const [got, kind] = last;
      const tail = head[1] === "142" ? "timeout" : "exit " + head[1];
      got[kind] = got[kind] === "" ? tail : got[kind] + "\n" + tail;
    }
  }
  return gots;
}

async function shard_run(shard: Test[], tag: number, node: number,
  fails: Fail[]): Promise<void> {
  const got = await lib.ssh(node, shard_script(shard, tag), shard_pack(shard),
    20 * 60 * 1000);
  fs.mkdirSync("/tmp/bend-test", { recursive: true });
  fs.writeFileSync("/tmp/bend-test/" + String(tag) + ".txt", got.out + got.err);
  if (!got.out.includes(MARK + " built")) {
    throw new Error("node");
  }
  const gots = shard_parse(shard, got.out);
  for (const t of shard) {
    fails.push(...test_judge(t, gots.get(t.name) ?? {}));
  }
}

// Main
// ====

if (import.meta.main) {
  const tests = fs.readdirSync(TESTS).sort().flatMap((dir) =>
    fs.readdirSync(path.join(TESTS, dir)).filter((f) => f.endsWith(".bend"))
      .sort().map((f) => test_read(dir, f)));
  const nodes = await lib.node_lock();
  const shards = shard_split(tests, nodes.length);
  const fails: Fail[] = [];
  await lib.node_pool(nodes, shards.map((shard, tag) => (node: number) =>
    shard_run(shard, tag, node, fails)));
  fails.sort((a, b) => a.name < b.name ? -1 : 1);
  if (!lib.GATE) {
    for (const f of fails) {
      console.log("FAIL " + f.name + " [" + f.probe + "]");
      console.log("  expected: " + f.want.replace(/\n/g, "\\n"));
      console.log("  observed: " + f.got.replace(/\n/g, "\\n"));
    }
  }
  const bad = new Set(fails.map((f) => f.name));
  lib.verdict(tests.length - bad.size, tests.length);
}
