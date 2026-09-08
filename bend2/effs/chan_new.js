// Chan
// ====
//! use ./chan.js

function chan_new(room) {
  const row = { room: Number(room), ring: [], wait: [], shut: false };
  return sys_get().mint("Chan", "chan", row);
}
