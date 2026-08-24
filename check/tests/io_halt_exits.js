function halt_probe() {
  setTimeout(() => {
    require("fs").writeSync(1, "zombie\n");
  }, 0);
  return { $: "Unit" };
}
