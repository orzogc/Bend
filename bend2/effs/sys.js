// Sys
// ===

function sys_get() {
  if (globalThis.BEND_SYS !== undefined) {
    return globalThis.BEND_SYS;
  }
  const ffi = require("bun:ffi");
  const mac = process.platform === "darwin";
  const err = mac ? "__error" : "__errno_location";
  const lib = ffi.dlopen(mac ? "libSystem.dylib" : "libc.so.6", {
    socket: { args: ["i32", "i32", "i32"], returns: "i32" },
    bind: { args: ["i32", "ptr", "u32"], returns: "i32" },
    listen: { args: ["i32", "i32"], returns: "i32" },
    connect: { args: ["i32", "ptr", "u32"], returns: "i32" },
    accept: { args: ["i32", "ptr", "ptr"], returns: "i32" },
    send: { args: ["i32", "ptr", "u64", "i32"], returns: "i64" },
    recv: { args: ["i32", "ptr", "u64", "i32"], returns: "i64" },
    read: { args: ["i32", "ptr", "u64"], returns: "i64" },
    sendto: {
      args: ["i32", "ptr", "u64", "i32", "ptr", "u32"],
      returns: "i64",
    },
    recvfrom: {
      args: ["i32", "ptr", "u64", "i32", "ptr", "ptr"],
      returns: "i64",
    },
    close: { args: ["i32"], returns: "i32" },
    poll: { args: ["ptr", "u32", "i32"], returns: "i32" },
    setsockopt: { args: ["i32", "i32", "i32", "ptr", "u32"], returns: "i32" },
    strerror: { args: ["i32"], returns: "cstring" },
    getenv: { args: ["ptr"], returns: "ptr" },
    [err]: { args: [], returns: "ptr" },
  });
  const sys = {
    s: lib.symbols,
    ptr: ffi.ptr,
    rows: [],
    free: [],
    SOCK_STREAM: 1,
    SOCK_DGRAM: 2,
    EILSEQ: mac ? 92 : 84,
    errno() {
      return ffi.read.i32(lib.symbols[err](), 0);
    },
    fail(code) {
      const text = String(lib.symbols.strerror(code));
      return { $: "Fail", error: { $: "Tuple", fst: code >>> 0, snd: text } };
    },
    done(value) {
      return { $: "Done", value: value };
    },
    tup(...xs) {
      let out = xs[xs.length - 1];
      for (let i = xs.length - 2; i >= 0; i--) {
        out = { $: "Tuple", fst: xs[i], snd: out };
      }
      return out;
    },
    mint(ctr, kind, fd) {
      const slot = this.free.length > 0 ? this.free.pop() : this.rows.length;
      if (slot === 4096) {
        throw "bend: error 1: the handle table is full";
      }
      const row = this.rows[slot];
      const gen = row === undefined ? 1 : (row.gen + 1) >>> 0;
      this.rows[slot] = { gen: gen, kind: kind, fd: fd };
      return { $: ctr, slot: slot, gen: gen };
    },
    read(handle, kind) {
      const row = this.rows[Number(handle.slot)];
      if (row === undefined || row.gen !== Number(handle.gen)) {
        return null;
      }
      if (row.fd === null || !kind.includes(row.kind)) {
        return null;
      }
      return row.fd;
    },
    kill(handle) {
      const row = this.rows[Number(handle.slot)];
      if (row === undefined || row.gen !== Number(handle.gen)) {
        return null;
      }
      if (row.fd === null) {
        return null;
      }
      const fd = row.fd;
      row.fd = null;
      row.kind = null;
      this.free.push(Number(handle.slot));
      return fd;
    },
    sock(type) {
      return this.s.socket(2, type, 0);
    },
    reuse(fd) {
      const one = new Int32Array([1]);
      const level = mac ? 0xffff : 1;
      const name = mac ? 0x0004 : 2;
      this.s.setsockopt(fd, level, name, this.ptr(one), 4);
    },
    poll(polls, ms) {
      const buf = new Int32Array(polls.length * 2);
      polls.forEach((w, i) => {
        buf[2 * i] = w.fd;
        buf[2 * i + 1] = 1;
      });
      const n = this.s.poll(this.ptr(buf), polls.length, ms);
      return polls.filter((w, i) => n > 0 && (buf[2 * i + 1] >>> 16) !== 0);
    },
    addr(host, port) {
      const part = host.split(".");
      const deci = (p) => /^(0|[1-9][0-9]{0,2})$/.test(p) && Number(p) < 256;
      if (port > 65535 || part.length !== 4 || !part.every(deci)) {
        return null;
      }
      const b = new Uint8Array(16);
      b[0] = mac ? 16 : 2;
      b[1] = mac ? 2 : 0;
      b[2] = (port >> 8) & 255;
      b[3] = port & 255;
      b.set(part.map(Number), 4);
      return b;
    },
    addr_show(b) {
      const host = b[4] + "." + b[5] + "." + b[6] + "." + b[7];
      return { host: host, port: (b[2] << 8) | b[3] };
    },
    bytes(text) {
      const b = [];
      for (const c of text) {
        b.push(c.codePointAt(0) & 255);
      }
      return Uint8Array.from(b);
    },
    text(b, n) {
      let out = "";
      for (let i = 0; i < n; i++) {
        out += String.fromCharCode(b[i]);
      }
      return out;
    },
    name(text) {
      return Uint8Array.from([...this.bytes(text), 0]);
    },
    cstr(at) {
      let out = "";
      for (let i = 0; ffi.read.u8(at, i) !== 0; i++) {
        out += String.fromCharCode(ffi.read.u8(at, i));
      }
      return out;
    },
  };
  globalThis.BEND_SYS = sys;
  return sys;
}
