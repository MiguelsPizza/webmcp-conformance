#!/usr/bin/env bash
# Re-record the corpus against the current model and name it after spec commit $1.
# Keeps the old corpus's seed and trace count, so the diff shows only what the model change did.
# Also updates the corpus path in README.md. Prints how many traces changed.
set -euo pipefail
cd "$(dirname "$0")/../.."
spec=$1
shopt -s nullglob
old=(corpus/spec-*.json)
[ "${#old[@]}" -eq 1 ] || { echo "expected exactly one corpus/spec-*.json" >&2; exit 1; }
old=${old[0]}
new=corpus/spec-$spec.json
prev=$(mktemp --suffix=.json)
cp "$old" "$prev"
read -r seed count < <(node -e 'const c=require(process.argv[1]);console.log(c.seed,c.traces.length)' "$prev")
rm "$old"
lake build oracle >/dev/null
node harness/run.cjs --record "$new" "$count" "$seed" >/dev/null
node -e '
  const fs = require("node:fs");
  const [file, spec, prevFile] = process.argv.slice(1);
  const c = JSON.parse(fs.readFileSync(file, "utf8"));
  c.spec = spec;
  fs.writeFileSync(file, JSON.stringify(c) + "\n");
  const prev = JSON.parse(fs.readFileSync(prevFile, "utf8")).traces;
  const changed = c.traces.filter((t, i) => JSON.stringify(t) !== JSON.stringify(prev[i])).length;
  console.log(`${changed} of ${c.traces.length} traces changed`);
' "$new" "$spec" "$prev"
# Point the README's replay commands at the new file.
sed -i "s#$old#$new#g" README.md
