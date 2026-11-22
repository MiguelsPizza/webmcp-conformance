#!/usr/bin/env bash
# The gate every model change has to pass:
#   1. the model and every proof build, with no warnings (so no `sorry`)
#   2. the proofs rest only on Lean's standard axioms
#   3. the recorded corpus is exactly what the model says, so a model change can't land
#      without the expected outcomes it implies
# Prints a short report to stdout and exits non-zero on the first failure.
set -uo pipefail
cd "$(dirname "$0")/../.."

log=$(mktemp)
if ! lake build --wfail WebMCP oracle >"$log" 2>&1; then
  cat "$log"
  echo "FAIL lake build --wfail"
  exit 1
fi
echo "ok   lake build --wfail (model, proofs, oracle)"

axioms=$(grep -E "depends on axioms|does not depend on any axioms" "$log" || true)
if [ -z "$axioms" ]; then
  echo "FAIL no #print axioms output; Proofs.lean should end with #print axioms lines"
  exit 1
fi
extra=$(sed -nE 's/.*depends on axioms: \[(.*)\]/\1/p' <<<"$axioms" | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' | sort -u || true)
if [ -n "$extra" ]; then
  echo "$axioms"
  echo "FAIL proofs use non-standard axioms: $(tr '\n' ' ' <<<"$extra")"
  exit 1
fi
echo "ok   $(wc -l <<<"$axioms" | tr -d ' ') theorems use only propext, Classical.choice, Quot.sound"

shopt -s nullglob
corpora=(corpus/spec-*.json)
if [ "${#corpora[@]}" -ne 1 ]; then
  echo "FAIL expected exactly one corpus/spec-*.json, found ${#corpora[@]}"
  exit 1
fi
corpus=${corpora[0]}
read -r seed count < <(node -e 'const c=require(process.argv[1]);console.log(c.seed,c.traces.length)' "$PWD/$corpus")
fresh=$(mktemp --suffix=.json)
node harness/run.cjs --record "$fresh" "$count" "$seed" >/dev/null
if ! node -e '
  const [a, b] = process.argv.slice(1).map((f) => require(f).traces);
  const diff = a.filter((t, i) => JSON.stringify(t) !== JSON.stringify(b[i])).length;
  if (diff) { console.log(`FAIL ${diff} of ${a.length} corpus traces differ from what the model now says`); process.exit(1); }
' "$PWD/$corpus" "$fresh"; then
  echo "     re-record it: node harness/run.cjs --record $corpus $count $seed"
  exit 1
fi
echo "ok   $corpus matches the model ($count traces, seed $seed)"
