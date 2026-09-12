// Audio
// =====

// A silent device: the ring's queue drains by the clock.
function audio_open(rate) {
  if (rate < 8000 || rate > 192000) {
    return io_fail(22);
  }
  const h = io_mint("Audio", "audio", { rate, queued: 0, at: Date.now() });
  return h === null ? io_fail(24) : io_done(h);
}
