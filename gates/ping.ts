#!/usr/bin/env bun
// The launcher, the installer, a release and the ping, on this machine: a
// hub.ts on a random localhost port with its log and DL_DIR in a temp dir,
// behind a Bun.serve that plays Caddy (/dl/* from DL_DIR, /ping to the
// hub), a release.ts --dry into that DL_DIR, an install.sh against it (Bun
// is here, so it installs nothing), then bend --help through the launcher.
// Checks: the help and the guide print, current points at app/<ver>, the log has the
// run's cmd, the disclosure printed once, a second release with a notice
// prints it and switches current, BEND_NO_TELEMETRY=1 logs no id.

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

import * as lib from "./_lib";

// Constants
// =========

const PORT   = 20000 + Math.floor(Math.random() * 40000);
const ORIGIN = "http://localhost:" + String(PORT);
const HUB    = "http://localhost:" + String(PORT + 1);
const TMP    = fs.mkdtempSync(path.join(os.tmpdir(), "bend-ping-"));
const HOME   = path.join(TMP, "home");
const DL     = path.join(TMP, "dl");
const LOG    = path.join(TMP, "log.jsonl");
const TELL   = "bend sends anonymous usage data and updates itself";

const fails: string[] = [];
let total = 0;

// Run
// ===

// the runs are async: the gate's own server answers them meanwhile
function run(bin: string, args: string[], env: Record<string, string>): Promise<lib.Exec> {
  return lib.exec(bin, args, undefined, 25_000, env);
}

function bend(args: string[], env: Record<string, string> = {}): Promise<lib.Exec> {
  return run(path.join(HOME, "bin", "bend"), args,
    { BEND_HOME: HOME, BEND_ORIGIN: ORIGIN, ...env });
}

function check(what: string, ok: boolean): void {
  total += 1;
  if (!ok) {
    fails.push(what);
  }
}

function logs(): Record<string, unknown>[] {
  return fs.readFileSync(LOG, "utf8").trim().split("\n")
    .map((l) => JSON.parse(l) as Record<string, unknown>);
}

async function hub_wait(): Promise<void> {
  for (let i = 0; i < 50; i += 1) {
    try {
      await fetch(HUB + "/");
      return;
    } catch {
      await new Promise((wake) => setTimeout(wake, 100));
    }
  }
  throw new Error("hub.ts did not come up on " + HUB);
}

const caddy = Bun.serve({
  port: PORT,
  fetch(req) {
    const at = new URL(req.url).pathname;
    if (at.startsWith("/dl/")) {
      return new Response(Bun.file(path.join(DL, path.basename(at))));
    }
    return fetch(HUB + at, { method: req.method, body: req.body });
  },
});

// Main
// ====

const hub = child.spawn(process.execPath, [path.join(lib.ROOT, "front", "hub.ts")],
  { stdio: "ignore", env: { ...process.env, HUB_PORT: String(PORT + 1),
    HUB_STORE: path.join(TMP, "store"), PING_LOG: LOG, DL_DIR: DL } });
try {
  await hub_wait();
  const rel = await run(process.execPath, [path.join(lib.ROOT, "front", "release.ts"),
    "--dry"], { DL_DIR: DL, BEND_ORIGIN: ORIGIN });
  check("release.ts --dry: " + rel.err, rel.code === 0);
  const latest = JSON.parse(fs.readFileSync(path.join(DL, "latest.json"),
    "utf8")) as { ver: string; url: string; sha256: string };
  const ins = await run("sh", [path.join(lib.ROOT, "front", "install.sh")],
    { BEND_HOME: HOME, BEND_ORIGIN: ORIGIN });
  check("install.sh: " + ins.err, ins.code === 0);
  check("the disclosure printed once", ins.err.split(TELL).length === 2);
  check("the install updated to " + latest.ver,
    ins.err.includes("bend updated to " + latest.ver));
  check("current -> app/" + latest.ver,
    fs.readlinkSync(path.join(HOME, "current")) === "app/" + latest.ver);
  const guide = await bend(["guide"]);
  check("bend guide prints the guide", guide.code === 0 && guide.out.includes("# "));
  const help = await bend(["--help"]);
  check("bend --help prints the help", help.code === 0 && help.out.includes("usage:"));
  check("no disclosure on the second run", !help.err.includes(TELL));
  const line = logs().pop() ?? {};
  check("the log has cmd --help", line.cmd === "--help" && line.ver === latest.ver
    && typeof line.id === "string" && line.exit === 0 && typeof line.ms === "number");
  fs.copyFileSync(path.join(DL, latest.ver + ".tar.gz"), path.join(DL, "v2.tar.gz"));
  fs.writeFileSync(path.join(DL, "latest.json"), JSON.stringify({ ver: "v2",
    url: ORIGIN + "/dl/v2.tar.gz", sha256: latest.sha256, notice: "hello from v2" }));
  const next = await bend(["--help"]);
  check("the notice prints", next.err.includes("hello from v2"));
  check("the launcher updated to v2", next.code === 0
    && next.err.includes("bend updated to v2")
    && fs.readlinkSync(path.join(HOME, "current")) === "app/v2");
  const mute = await bend(["--help"], { BEND_NO_TELEMETRY: "1" });
  const last = logs().pop() ?? {};
  check("BEND_NO_TELEMETRY=1 logs no id", mute.code === 0 && last.id === undefined
    && last.exit === undefined && last.cmd === "--help" && last.ver === "v2");
} catch (e) {
  check(String(e), false);
} finally {
  hub.kill();
  caddy.stop(true);
  fs.rmSync(TMP, { recursive: true, force: true });
}
if (!lib.GATE) {
  for (const f of fails) {
    console.log("FAIL " + f);
  }
}
lib.verdict(total - fails.length, total);
