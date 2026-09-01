// The bun plugin: makes `import * as Game from "./file.bend"` work.
//
// Register it once and every .bend import compiles on the fly:
//
//   bunfig.toml           preload = ["bend-lang/plugin"]     (bun run)
//   [serve.static]        plugins = ["bend-lang/plugin"]     (bun ./page.html)
//   Bun.build({plugins})  import bend from "bend-lang/plugin" (bundling)
//
// A .bend module exports every filled, non-base, non-IO def, wrapped so a
// JS caller passes only the live (non-erased) arguments and gets a plain
// value back. Constructors are `{$: "Name", field: value, ...}`, closures
// are plain functions, Nat is BigInt, Bool/String/U32 are native.

import { plugin, type BunPlugin } from "bun";

import * as Bend from "./bend.ts";
import * as Comp from "./comp.ts";

const bend: BunPlugin = {
  name: "bend",
  setup(build) {
    build.onLoad({ filter: /\.bend$/ }, async (args) => {
      const book = Bend.book_nil();
      try {
        await Bend.book_load(book, args.path, "", new Map());
        Bend.book_valid(book);
      } catch (e) {
        const err = e as Bend.Err;
        throw new Error(err !== null && typeof err === "object"
          && err.$ === "Err" ? Bend.err_show(err) : String(e));
      }
      if (book.hols > 0) {
        throw new Error(args.path + " has TODOs and cannot compile");
      }
      const outs = [...new Set(book.order)].filter((k) => {
        const tld = book.tlds[k];
        return tld.$ === "Def" && tld.v !== null && tld.b !== true
          && tld.i === undefined && Comp.io_base(book, tld.T) === null;
      });
      return { contents: Comp.js_lib(book, outs), loader: "js" };
    });
  },
};

export default bend;
plugin(bend);
