// Renders the film. Usage:
//   node video.js            docs/intro.mp4 (1280x720, 30fps) and docs/intro.gif (640px wide, 30fps; the cube at 15)
//   node video.js 3 9 26     stills at those seconds into shots/
// Frames stream straight into ffmpeg; nothing lands on disk but the outputs.
const { createCanvas } = require("canvas");
const fs = require("fs"), path = require("path"), { spawn, spawnSync } = require("child_process");
const { draw, setCtx, DUR, SCENES, T0 } = require("./render.js");

const W = 1280, H = 720, FPS = 30, OUT = path.join(__dirname, "..", "..", "docs");
const cv = createCanvas(W, H);
setCtx(cv.getContext("2d"));

const args = process.argv.slice(2);
if (args.length) {
  fs.mkdirSync("shots", { recursive: true });
  for (const a of args) {
    draw(parseFloat(a));
    fs.writeFileSync(`shots/t${a}.png`, cv.toBuffer("image/png"));
    console.log(`shots/t${a}.png`);
  }
} else (async () => {
  const mp4 = path.join(OUT, "intro.mp4"), gif = path.join(OUT, "intro.gif"), N = Math.round(DUR*FPS);
  const ff = spawn("ffmpeg", ["-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "bgra", "-s", `${W}x${H}`,
    "-r", String(FPS), "-i", "-", "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18", "-movflags", "+faststart", mp4],
    { stdio: ["pipe", "ignore", "inherit"] });
  for (let f = 0; f < N; f++) {
    draw(f/FPS);
    if (!ff.stdin.write(cv.toBuffer("raw"))) await new Promise(r => ff.stdin.once("drain", r));
    if (f % 900 === 0) console.log(`${f}/${N}`);
  }
  ff.stdin.end();
  await new Promise(r => ff.on("close", r));
  // the gif: one 64-colour palette for the whole film, ordered dither, frames
  // diffed by ffmpeg, 640px (the README column) at the film's 30fps. The
  // cube's camera moves change every pixel every frame and would cost 13 MB
  // alone, so its beats keep every other frame: the whole stays under 10 MB
  const names = SCENES.map(s => s[0]), a = T0[names.indexOf("dist")], j = names.indexOf("reduce"), b = T0[j] + SCENES[j][1];
  spawnSync("ffmpeg", ["-y", "-loglevel", "error", "-i", mp4, "-vf",
    `select='if(between(t,${a.toFixed(1)},${b.toFixed(1)}),not(mod(n,2)),1)',` +
    "scale=640:-1:flags=lanczos,split[a][b];[a]palettegen=max_colors=64[p];[b][p]paletteuse=dither=bayer:bayer_scale=5",
    "-fps_mode", "vfr", gif], { stdio: "inherit" });
  console.log("done: " + mp4 + " " + gif);
})();
