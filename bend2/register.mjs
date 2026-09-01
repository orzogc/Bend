// The node loader: makes `import Game from "./file.bend"` work under node.
//
//   node --import bend-lang/register app.mjs
//
// Loading a book may fetch a published package, so the hook is async and
// runs on node's hooks thread: on the main thread this file registers
// itself, on the hooks thread it is the hooks module. One hook: .bend files
// compile through the bend compiler, and this package's own .ts sources,
// which the hooks thread imports to do so, load through node's type
// stripper (node does not strip types under node_modules on its own). Same
// module shape and value conventions as the bun plugin.

import { register, stripTypeScriptTypes } from "node:module";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { isMainThread } from "node:worker_threads";

const HOME = new URL(".", import.meta.url).href;

if (isMainThread) {
  register(import.meta.url);
}

export async function load(url, context, nextLoad) {
  if (url.startsWith(HOME) && url.endsWith(".ts")) {
    const source = stripTypeScriptTypes(readFileSync(fileURLToPath(url),
      "utf8"));
    return { format: "module", source, shortCircuit: true };
  }
  if (!url.endsWith(".bend")) {
    return nextLoad(url, context);
  }
  const Bend = await import("./bend.ts");
  const Comp = await import("./comp.ts");
  const book = Bend.book_nil();
  try {
    await Bend.book_load(book, fileURLToPath(url), "", new Map());
    Bend.book_valid(book);
  } catch (e) {
    throw new Error(e !== null && typeof e === "object" && e.$ === "Err"
      ? Bend.err_show(e) : String(e));
  }
  if (book.hols > 0) {
    throw new Error(url + " has TODOs and cannot compile");
  }
  const outs = [...new Set(book.order)].filter((k) => {
    const tld = book.tlds[k];
    return tld.$ === "Def" && tld.v !== null && tld.b !== true
      && tld.i === undefined && Comp.io_base(book, tld.T) === null;
  });
  const source = Comp.js_lib(book, outs);
  return { format: "module", source, shortCircuit: true };
}
