// safe.ts's node side: runs `bend <f> --safe` on each file named on
// stdin, PAR at a time, each capped at CAP s, and prints one JSON array
// of { f, code, ms, out }
import * as child from "node:child_process";
import * as fs from "node:fs";

const files = fs.readFileSync(0, "utf8").split("\n").filter((l) => l !== "");
const CAP = Number(process.env.CAP ?? 30) * 1000;
const res: unknown[] = [];

function one(f: string): Promise<void> {
  return new Promise((done) => {
    const kid = child.spawn(process.execPath, ["bend2/main.ts", f, "--safe"], { env: process.env });
    let txt = "";
    kid.stdout.on("data", (d) => { txt += d; });
    kid.stderr.on("data", (d) => { txt += d; });
    const t0 = Date.now();
    const bomb = setTimeout(() => kid.kill("SIGKILL"), CAP);
    kid.on("close", (code) => {
      clearTimeout(bomb);
      const m = /BendTT: In (\S+):\naffine live code/.exec(txt);
      if (m !== null) {
        const d = child.spawnSync(process.execPath, ["gates/safe_diag.ts", f.replace(/\.bend$/, ".bendtt"), m[1]], { encoding: "utf8", timeout: 20000 });
        txt = txt.replace("affine live code, calls that descend", "affine live code, calls that descend: " + (d.stdout + d.stderr).trim().slice(0, 300));
      }
      res.push({ f, code, ms: Date.now() - t0, out: txt.slice(0, 1500) });
      done();
    });
  });
}

let next = 0;
await Promise.all(Array.from({ length: Number(process.env.PAR ?? 8) }, async () => {
  while (next < files.length) {
    await one(files[next++]);
  }
}));
process.stdout.write(JSON.stringify(res));
