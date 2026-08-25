// IO
// ==
//! use ./sys.js

function io_get_env(name) {
  const sys = sys_get();
  const key = sys.name(name);
  if (key.indexOf(0) < key.length - 1) {
    return sys.fail(2);
  }
  const at = sys.s.getenv(sys.ptr(key));
  if (at === null || at === 0) {
    return sys.fail(2);
  }
  return sys.done(sys.cstr(at));
}
