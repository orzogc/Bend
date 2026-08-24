function out_probe() {
  const ffi = require("bun:ffi");
  const mac = process.platform === "darwin";
  const lib = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6", {
    close: { args: ["i32"], returns: "i32" },
  });
  lib.symbols.close(1);
  return 0;
}
