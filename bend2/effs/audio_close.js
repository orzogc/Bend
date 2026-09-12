// Audio
// =====

function audio_close(audio) {
  io_kill(audio);
  return { $: "Unit" };
}
