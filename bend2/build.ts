#!/usr/bin/env bun
// The bundler: `bend-build <entry> [outdir]` bundles an entrypoint (a .html
// page or a .js/.ts module) for the browser, compiling every imported .bend
// file through the bend plugin. The bun CLI cannot load plugins, so this
// small driver exists to make the production build a one-liner.

import bend from "./plugin.ts";

const [entry, outdir] = process.argv.slice(2);
if (entry === undefined) {
  console.error("usage: bend-build <entry> [outdir]");
  process.exit(1);
}

const out = await Bun.build({
  entrypoints: [entry],
  outdir: outdir ?? "dist",
  target: "browser",
  minify: true,
  plugins: [bend],
});
for (const a of out.outputs) {
  console.log(a.path + " (" + (a.size / 1024).toFixed(1) + "kb)");
}
