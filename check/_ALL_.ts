#!/usr/bin/env bun

declare const process: {
  argv: string[];
  execPath: string;
  exit(code?: number): never;
  kill(pid: number, signal?: string): void;
  once(event: string, listener: () => void): void;
};

// Types
// =====

export type Text = {
  on(event: "data", listener: (s: string) => void): void;
};

export type Pipe = { setEncoding(encoding: "utf8"): Text };

export type Kid = {
  pid?: number;
  stdout: Pipe;
  stderr: Pipe;
  on(event: "error", listener: (e: Error) => void): void;
  on(event: "close", listener: (code: number | null) => void): void;
  kill(signal?: string): boolean;
};

export type Gate = { name: string; ok: boolean; secs: number; out: string };

// Constants
// =========

const child = import.meta.require("child_process") as {
  spawn(cmd: string, args: string[], opts?: {
    cwd?: string;
    stdio?: (string | null)[] | string;
    detached?: boolean;
  }): Kid;
};

const path = import.meta.require("path") as {
  join(...parts: string[]): string;
};

const HERE = process.argv.includes("--here");

const BUDGET = HERE ? 120 : 90;

// Gate
// ====

export function gate_spawn(name: string,
  kids: Kid[]): Promise<Gate> {
  return new Promise((resolve) => {
    const at = performance.now();
    const flag = HERE && name === "perf" ? ["--here"] : [];
    const args = [path.join(import.meta.dirname, name + ".ts"), ...flag];
    const kid = child.spawn(process.execPath, args,
      { detached: true, stdio: ["ignore", "pipe", "pipe"] });
    kids.push(kid);
    let out = "";
    let err = "";
    kid.stdout.setEncoding("utf8").on("data", (s) => {
      out += s;
    });
    kid.stderr.setEncoding("utf8").on("data", (s) => {
      err += s;
    });
    kid.on("error", (e) => {
      const secs = (performance.now() - at) / 1000;
      resolve({ name, ok: false, secs, out: String(e) });
    });
    kid.on("close", (code) => {
      const secs = (performance.now() - at) / 1000;
      const lines = out.trimEnd().split("\n");
      const ok = code === 0 && lines[lines.length - 1] === "PASSED";
      resolve({ name, ok, secs, out: out + err });
    });
  });
}

export function gate_kill(kids: Kid[]): void {
  for (const kid of kids) {
    try {
      process.kill(-(kid.pid as number), "SIGKILL");
    } catch {}
  }
}

export function gate_show(g: Gate): boolean {
  const mark = g.ok ? "PASS " : "FAIL ";
  console.log(mark + g.name.padEnd(6) + g.secs.toFixed(1) + "s");
  if (!g.ok) {
    for (const line of g.out.split("\n")) {
      if (!line.startsWith("PASS ") && line !== "") {
        console.log("  " + line);
      }
    }
  }
  return g.ok;
}

export async function gate_run(): Promise<boolean> {
  const start = performance.now();
  const waves: string[][] = HERE
    ? [["perf"], ["repo", "test"]]
    : [["perf", "repo", "test"]];
  const names = waves.flat();
  const kids: Kid[] = [];
  const gates: Gate[] = [];
  let bomb: ReturnType<typeof setTimeout> | undefined = undefined;
  const runs = (async (): Promise<Gate[]> => {
    for (const wave of waves) {
      await Promise.all(wave.map(async (name) => {
        gates.push(await gate_spawn(name, kids));
      }));
    }
    return gates;
  })();
  process.once("SIGINT", () => {
    gate_kill(kids);
    process.exit(130);
  });
  const wait = new Promise<null>((resolve) => {
    bomb = setTimeout(() => {
      resolve(null);
    }, BUDGET * 1000);
  });
  const all = await Promise.race([runs, wait]);
  clearTimeout(bomb);
  if (all === null) {
    const done = new Set(gates.map((g) => g.name));
    const late = names.filter((name) => !done.has(name));
    gate_kill(kids);
    console.log("FAIL gate   the " + BUDGET + "s budget is spent" +
      " (still running or queued: " + late.join(", ") +
      ") -- all checks aborted");
    const secs = ((performance.now() - start) / 1000).toFixed(1);
    console.log("\nUNHEALTHY (" + secs + "s)");
    return false;
  }
  let ok = true;
  for (const name of names) {
    ok = gate_show(all.find((g) => g.name === name) as Gate) && ok;
  }
  const secs = ((performance.now() - start) / 1000).toFixed(1);
  console.log((ok ? "\nHEALTHY" : "\nUNHEALTHY") + " (" + secs + "s)");
  return ok;
}

// Main
// ====

if (import.meta.main) {
  if (process.argv.length > (HERE ? 3 : 2)) {
    console.error("Usage: bun check/_ALL_.ts [--here]");
    process.exit(1);
  }
  process.exit(await gate_run() ? 0 : 1);
}
