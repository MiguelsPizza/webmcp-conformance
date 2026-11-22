#!/usr/bin/env node
// Scores the model against the web-platform-tests for WebMCP.
//
//   node tools/wpt-score.cjs [--oracle <path>] [--cases <path>] [--verbose]
//
// Runs every translated subtest in wpt/cases.json through the oracle and compares the model's
// outcomes with what the WPT assertions require. Prints, per file and in total, how many
// subtests agree, disagree, are not expressible in the model, or are out of its scope; then
// every disagreeing check with its recorded classification.
//
// Exits non-zero if a disagreement has no recorded classification, or a check recorded as a
// disagreement now agrees: either means cases.json and the model have drifted apart.
"use strict";
const fs = require("fs");
const path = require("path");
const { execFileSync } = require("child_process");

const args = process.argv.slice(2);
const opt = (k, d) => { const i = args.indexOf(k); return i >= 0 ? args[i + 1] : d; };
const root = path.join(__dirname, "..");
const oracle = opt("--oracle", path.join(root, ".lake/build/bin/oracle"));
const casesPath = opt("--cases", path.join(root, "wpt/cases.json"));
const verbose = args.includes("--verbose");

const doc = JSON.parse(fs.readFileSync(casesPath, "utf8"));
if (!fs.existsSync(oracle)) {
  console.error(`no oracle at ${oracle}; run \`lake build WebMCP oracle\` or pass --oracle`);
  process.exit(2);
}

// One oracle process for every trace: one JSON array per line in, one per line out.
const jobs = [];
for (const s of doc.subtests) {
  if (s.scope !== "in") continue;
  if (s.trace.length) jobs.push({ s, which: "main", ops: [...(s.setup || []), ...s.trace], skip: (s.setup || []).length });
  if (s.extra) jobs.push({ s, which: "extra", ops: s.extra.trace, skip: 0 });
}
const lines = execFileSync(oracle, { input: jobs.map((j) => JSON.stringify(j.ops)).join("\n") + "\n" })
  .toString().trim().split("\n");
if (lines.length !== jobs.length) throw new Error(`oracle answered ${lines.length} of ${jobs.length} traces`);
jobs.forEach((j, i) => { (j.s._got ||= {})[j.which] = JSON.parse(lines[i]).slice(j.skip); });

// A getTools() outcome as a list of {name, title, description, inputSchema, outputSchema, annotations}.
function parseTools(o) {
  if (!o.startsWith("tools:")) return null;
  const body = o.slice("tools:".length);
  if (!body) return [];
  return body.split(";").map((t) => {
    const f = t.split("|");
    if (f.length !== 6) throw new Error(`cannot split tool ${JSON.stringify(t)}`);
    const [name, title, description, inputSchema, outputSchema, annotations] = f;
    return { name, title, description, inputSchema, outputSchema, annotations };
  });
}
const deepEqual = (a, b) => JSON.stringify(sortKeys(a)) === JSON.stringify(sortKeys(b));
function sortKeys(v) {
  if (Array.isArray(v)) return v.map(sortKeys);
  if (v && typeof v === "object") return Object.fromEntries(Object.keys(v).sort().map((k) => [k, sortKeys(v[k])]));
  return v;
}

// Whether outcome `got` satisfies `want`; returns [ok, what the model said].
function evaluate(want, got) {
  if (got === undefined) return [false, "(no outcome)"];
  if ("outcome" in want) return [got === want.outcome, got];
  const tools = parseTools(got);
  if (!tools) return [false, got];
  if ("names" in want) { const n = tools.map((t) => t.name); return [deepEqual(n, want.names), "names " + JSON.stringify(n)]; }
  if ("count" in want) return [tools.length === want.count, "count " + tools.length];
  const t = tools.find((x) => x.name === want.tool);
  if (!t) return [false, `no tool ${want.tool}`];
  const v = t[want.field];
  const shown = `${want.tool}.${want.field} = ${v}`;
  if (want.isNull) return [v === "null", shown];
  if (want.notNull) return [v !== "null", shown];
  if ("json" in want) return [v !== "null" && deepEqual(JSON.parse(v), want.json), shown];
  if ("path" in want) return [v !== "null" && JSON.parse(v)?.[want.path] === want.equals, shown];
  if ("equals" in want) return [v === want.equals, shown];
  throw new Error("unknown expectation " + JSON.stringify(want));
}

const STATUS = ["agree", "disagree", "not expressible", "out of scope"];
const perFile = new Map();
const total = Object.fromEntries(STATUS.map((k) => [k, 0]));
const checkTotals = { agree: 0, disagree: 0, proxied: 0, notExpressible: 0 };
const disagreements = [];
const problems = [];
let partial = 0;

for (const s of doc.subtests) {
  let status;
  if (s.scope !== "in") status = "out of scope";
  else {
    let anyDisagree = false, anyReal = false;
    const groups = [["main", s.checks], ["extra", s.extra ? s.extra.checks : []]];
    for (const [which, checks] of groups) for (const c of checks) {
      const [ok, said] = evaluate(c.want, (s._got?.[which] || [])[c.at]);
      if (!c.setup) anyReal = true;
      if (c.proxy) checkTotals.proxied++;
      checkTotals[ok ? "agree" : "disagree"]++;
      if (!ok) {
        anyDisagree = true;
        disagreements.push({ s, c, said });
        if (!c.expectDisagree) problems.push(`unclassified disagreement: ${s.file} L${c.line} (${c.assert}): model ${said}`);
      } else if (c.expectDisagree) {
        problems.push(`recorded as a disagreement but now agrees: ${s.file} L${c.line} (${c.assert})`);
      }
      if (verbose) console.log(`${ok ? "agree   " : "DISAGREE"} ${s.file} L${c.line}: ${c.assert} -> model ${said}`);
    }
    checkTotals.notExpressible += (s.notExpressible || []).length;
    status = anyDisagree ? "disagree" : anyReal ? "agree" : "not expressible";
    if (status !== "not expressible" && (s.notExpressible || []).length) partial++;
  }
  const f = perFile.get(s.file) || Object.fromEntries(STATUS.map((k) => [k, 0]));
  f[status]++; perFile.set(s.file, f); total[status]++;
}

const pad = (x, n) => String(x).padEnd(n);
const padL = (x, n) => String(x).padStart(n);
const W = Math.max(...[...perFile.keys()].map((k) => k.length)) + 2;
console.log(`WPT ${doc.wpt.commit.slice(0, 12)}  spec ${doc.spec.commit}  oracle ${path.relative(process.cwd(), oracle) || oracle}\n`);
console.log(pad("file", W) + STATUS.map((k) => padL(k, 17)).join(""));
for (const [file, f] of [...perFile].sort()) {
  if (!verbose && f["out of scope"] === Object.values(f).reduce((a, b) => a + b, 0)) continue;
  console.log(pad(file, W) + STATUS.map((k) => padL(f[k] || "", 17)).join(""));
}
const outOnly = [...perFile.values()].filter((f) => f["out of scope"] === Object.values(f).reduce((a, b) => a + b, 0));
if (!verbose) console.log(pad(`(${outOnly.length} files entirely out of scope)`, W) + padL("", 51) + padL(outOnly.reduce((a, f) => a + f["out of scope"], 0), 17));
console.log(pad("total", W) + STATUS.map((k) => padL(total[k], 17)).join(""));
console.log(`\n${doc.subtests.length} subtests in ${perFile.size} files; ${partial} of the agreeing/disagreeing subtests also have assertions the model cannot express.`);
console.log(`checks: ${checkTotals.agree} agree, ${checkTotals.disagree} disagree (${checkTotals.proxied} use a proxy value); ${checkTotals.notExpressible} assertions not expressible.`);

if (disagreements.length) {
  console.log("\nDisagreements:");
  for (const { s, c, said } of disagreements) {
    const k = c.expectDisagree;
    console.log(`  ${s.file} L${c.line}: ${c.assert}\n    WPT wants ${JSON.stringify(c.want)}, model ${said}` +
      (k ? `\n    ${k.kind} ${k.ref || ""}: ${k.summary}` : "\n    UNCLASSIFIED"));
  }
}
if (problems.length) { console.log("\n" + problems.join("\n")); process.exit(1); }
