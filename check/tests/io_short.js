// IO
// ==

let short_left = -1;

function short_take() {
  if (short_left < 0) {
    return false;
  }
  if (short_left === 0) {
    short_left = -1;
    return true;
  }
  short_left -= 1;
  return false;
}

function short_arm(n) {
  const fs = require("fs");
  const real = fs.writeSync;
  fs.writeSync = function(...args) {
    if (short_take()) {
      const err = new Error("a write armed short by the test");
      err.code = "EIO";
      throw err;
    }
    return real.apply(fs, args);
  };
  short_left = n;
  return { $: "Unit" };
}
