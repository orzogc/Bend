// Window
// ======

function window_open(title, width, height) {
  const code = process.platform === "darwin" ? 45 : 95;
  const text = "Window.open: the JS backend has no display; build a binary" +
    " with -o";
  return { $: "Fail", error: { $: "Tuple", fst: code, snd: text } };
}
