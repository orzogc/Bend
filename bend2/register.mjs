// The node loader: makes `import Game from "./file.bend"` work under node.
//
//   node --import bend-lang/register app.mjs
//
// Two hooks: .bend files compile through the bend compiler, and this
// package's own .ts sources load through node's type stripper (node does
// not strip types under node_modules on its own). Same module shape and
// value conventions as the bun plugin.

import { createRequire, registerHooks, stripTypeScriptTypes }
  from "node:module";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const HOME = new URL(".", import.meta.url).href;
const require = createRequire(import.meta.url);

registerHooks({
  load(url, context, nextLoad) {
    if (url.startsWith(HOME) && url.endsWith(".ts")) {
      const source = stripTypeScriptTypes(readFileSync(fileURLToPath(url),
        "utf8"));
      return { format: "module", source, shortCircuit: true };
    }
    if (url.endsWith(".bend")) {
      const Bend = require("./bend.ts");
      const Comp = require("./comp.ts");
      const book = Bend.book_nil();
      try {
        Bend.book_load(book, fileURLToPath(url), "", new Map());
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
    return nextLoad(url, context);
  },
});
