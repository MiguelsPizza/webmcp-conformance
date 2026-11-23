// Re-ask the oracle for the outcomes of every repro in repros/ and rewrite each file's `want`,
// `comment.model` and `spec`. Prints how many repros' outcomes changed: for those, the
// `comment.observed` entries were recorded against the old model and need rechecking.
//
//   node tools/refresh-repros.cjs        (after `lake build oracle`)
const { execFileSync } = require("node:child_process");
const fs = require("node:fs");
const path = require("node:path");

const root = path.join(__dirname, "..");
const spec = JSON.parse(fs.readFileSync(path.join(root, "spec", "anchors.json"), "utf8")).spec;
const dir = path.join(root, "repros");
const files = fs.readdirSync(dir).filter((f) => f.endsWith(".json")).sort();
const input = files.map((f) => JSON.parse(fs.readFileSync(path.join(dir, f), "utf8")))
  .flatMap((r) => r.traces.map((t) => JSON.stringify(t.ops))).join("\n") + "\n";
const answers = execFileSync(path.join(root, ".lake", "build", "bin", "oracle"), { input, encoding: "utf8" })
  .trim().split("\n").map((l) => JSON.parse(l));
const changed = [];
for (const f of files) {
  const file = path.join(dir, f);
  const r = JSON.parse(fs.readFileSync(file, "utf8"));
  const before = JSON.stringify(r.traces.map((t) => t.want));
  for (const t of r.traces) t.want = answers.shift();
  if (JSON.stringify(r.traces.map((t) => t.want)) !== before) changed.push(f);
  r.spec = spec;
  r.comment.model = r.traces.map((t) => t.want.join("  /  ")).join("\n");
  fs.writeFileSync(file, JSON.stringify(r, null, 2) + "\n");
}
console.log(`${changed.length} of ${files.length} repros changed${changed.length ? `: ${changed.join(", ")}` : ""}`);
