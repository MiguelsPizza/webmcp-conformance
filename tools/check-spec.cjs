// Detects spec drift. Each entry of spec/anchors.json names a part of index.bs the model
// transcribes and the hash of its text at the spec commit the model reflects. This script
// re-extracts those parts from an index.bs and reports any whose text changed, so the model
// definition citing it (`Spec: #<anchor>` in WebMCP/Model.lean) gets re-read.
//
//   node tools/check-spec.cjs <index.bs>                  exit 1 if anything changed
//   node tools/check-spec.cjs <index.bs> --update <sha>   record new hashes for spec commit <sha>
const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");

const root = path.join(__dirname, "..");
const anchorsPath = path.join(root, "spec", "anchors.json");
const [specPath, flag, newSha] = process.argv.slice(2);
const spec = fs.readFileSync(specPath, "utf8");
const anchors = JSON.parse(fs.readFileSync(anchorsPath, "utf8"));
const model = fs.readFileSync(path.join(root, "WebMCP", "Model.lean"), "utf8");

// The element that holds `marker`: its enclosing <div algorithm> if there is one, otherwise
// the marker's paragraph through the end of the next <dl> or <table>.
function extract(marker) {
  const at = spec.indexOf(marker);
  if (at < 0) return null;
  const divs = /<div algorithm[^>]*>|<div\b[^>]*>|<\/div>/g;
  const stack = [];
  let m;
  while ((m = divs.exec(spec)) && m.index < at) {
    if (m[0] === "</div>") stack.pop();
    else stack.push({ start: m.index, algorithm: m[0].startsWith("<div algorithm") });
  }
  const outer = stack.find((d) => d.algorithm);
  if (outer) {
    let depth = 0;
    divs.lastIndex = outer.start;
    while ((m = divs.exec(spec))) {
      depth += m[0] === "</div>" ? -1 : 1;
      if (depth === 0) return spec.slice(outer.start, m.index + m[0].length);
    }
    return null;
  }
  const start = spec.lastIndexOf("\n\n", at) + 2;
  const ends = ["</dl>", "</table>"].map((t) => spec.indexOf(t, at)).filter((i) => i >= 0);
  return spec.slice(start, Math.min(...ends) + 8);
}
const hash = (text) =>
  crypto.createHash("sha256").update(text.replace(/\s+/g, " ").trim()).digest("hex").slice(0, 16);

let changed = 0;
for (const a of anchors.anchors) {
  const text = extract(a.marker);
  const h = text === null ? "missing" : hash(text);
  const cited = model.includes(`Spec: #${a.anchor}`);
  if (flag === "--update") {
    a.sha256 = h;
  } else if (h !== a.sha256) {
    changed++;
    console.log(`changed: #${a.anchor} (${a.marker}) ${a.sha256} -> ${h}`);
  }
  if (!cited) {
    changed++;
    console.log(`not cited in WebMCP/Model.lean: #${a.anchor}`);
  }
}
if (flag === "--update") {
  anchors.spec = newSha;
  fs.writeFileSync(anchorsPath, JSON.stringify(anchors, null, 2) + "\n");
  console.log(`recorded ${anchors.anchors.length} anchors for spec ${newSha}`);
} else {
  console.log(changed ? `${changed} problem(s) against spec ${anchors.spec}` : `all ${anchors.anchors.length} modelled parts match spec ${anchors.spec}`);
  process.exitCode = changed ? 1 : 0;
}
