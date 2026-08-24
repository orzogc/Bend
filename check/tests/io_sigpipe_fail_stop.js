function pipe_probe() {
  const ffi = require("bun:ffi");
  const mac = process.platform === "darwin";
  const lib = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6", {
    pipe:  { args: ["ptr"], returns: "i32" },
    dup2:  { args: ["i32", "i32"], returns: "i32" },
    close: { args: ["i32"], returns: "i32" },
  });
  const fds = new Int32Array(2);
  lib.symbols.pipe(ffi.ptr(fds));
  lib.symbols.dup2(fds[1], 1);
  lib.symbols.close(fds[0]);
  lib.symbols.close(fds[1]);
  return 0;
}
