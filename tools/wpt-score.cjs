#!/usr/bin/env node
// Scores the model against the web-platform-tests for WebMCP.
//
//   node tools/wpt-score.cjs [--oracle <path>] [--cases <path>] [--verbose]
//
// Runs every translated subtest in wpt/cases.json through the oracle and compares the model's
// outcomes with what the WPT assertions require. Prints, per file and in total, how many
// subtests agree, disagree, are not expressible in the model, or are out of its scope; then
// every disagreeing check with its recorded classification. Traces may run in any document of
// the model's frame tree and use `concurrent` operations; a check of one agrees only if every
// outcome the model allows satisfies it.
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

// The origin of each document of the model's frame tree (`harnessDocs` in WebMCP/Model.lean).
const DOC_ORIGINS = [0, 0, 2, 1, 1];

// A getTools() outcome as a list of {name, title, description, inputSchema, outputSchema,
// annotations, source}; `source` is the document a `Tool` came from when it is not the caller.
function parseTools(o) {
  if (!o.startsWith("tools:")) return null;
  const body = o.slice("tools:".length);
  if (!body) return [];
  return body.split(";").map((t) => {
    const m = t.match(/@(\d+)$/);
    const f = (m ? t.slice(0, -m[0].length) : t).split("|");
    if (f.length !== 6) throw new Error(`cannot split tool ${JSON.stringify(t)}`);
    const [name, title, description, inputSchema, outputSchema, annotations] = f;
    return { name, title, description, inputSchema, outputSchema, annotations, source: m ? Number(m[1]) : null };
  });
}
const deepEqual = (a, b) => JSON.stringify(sortKeys(a)) === JSON.stringify(sortKeys(b));
function sortKeys(v) {
  if (Array.isArray(v)) return v.map(sortKeys);
  if (v && typeof v === "object") return Object.fromEntries(Object.keys(v).sort().map((k) => [k, sortKeys(v[k])]));
  return v;
}
const schemaIs = (v, want) => want === null ? v === "null" : v !== "null" && deepEqual(JSON.parse(v), want);

// Whether one outcome `got` of an op run in document `doc` satisfies `want`; returns [ok, what
// the model said].
function evaluate1(want, got, doc) {
  if (got === undefined) return [false, "(no outcome)"];
  if ("outcome" in want) return [got === want.outcome, got];
  if ("resolves" in want) return [got.startsWith("result:"), got];
  const tools = parseTools(got);
  if (!tools) return [false, got];
  if ("names" in want) { const n = tools.map((t) => t.name); return [deepEqual(n, want.names), "names " + JSON.stringify(n)]; }
  if ("count" in want) return [tools.length === want.count, "count " + tools.length];
  if ("lacks" in want) return [!tools.some((t) => t.name === want.lacks), "names " + JSON.stringify(tools.map((t) => t.name))];
  const t = tools.find((x) => x.name === want.tool);
  if (!t) return [false, `no tool ${want.tool}`];
  if ("like" in want) {
    const e = want.like, origin = DOC_ORIGINS[t.source ?? doc];
    const ok = (e.name === undefined || t.name === e.name) && (e.description === undefined || t.description === e.description) &&
      (!("inputSchema" in e) || schemaIs(t.inputSchema, e.inputSchema)) && (!("outputSchema" in e) || schemaIs(t.outputSchema, e.outputSchema)) &&
      ("annotations" in e ? schemaIs(t.annotations, e.annotations) : t.annotations === "null") &&
      (!("origin" in e) || origin === e.origin);
    return [ok, `${[t.name, t.title, t.description, t.inputSchema, t.outputSchema, t.annotations].join("|")} origin ${origin}`];
  }
  const v = t[want.field];
  const shown = `${want.tool}.${want.field} = ${v}`;
  if (want.isNull) return [v === "null", shown];
  if (want.notNull) return [v !== "null", shown];
  if ("json" in want) return [v !== "null" && deepEqual(JSON.parse(v), want.json), shown];
  if ("path" in want) return [v !== "null" && JSON.parse(v)?.[want.path] === want.equals, shown];
  if ("equals" in want) return [v === want.equals, shown];
  throw new Error("unknown expectation " + JSON.stringify(want));
}

// A check of outcome `got`: of action `c.action` when the op is `concurrent`, and of every
// outcome when the spec allows several (`any:`). It agrees only if every allowed outcome does.
function evaluate(c, got, op) {
  let alts = got === undefined ? [undefined] : got.startsWith("any:") ? JSON.parse(got.slice(4)) : [got];
  if (c.action !== undefined) alts = alts.map((a) => a && a.startsWith("all:") ? JSON.parse(a.slice(4))[c.action] : undefined);
  alts = [...new Set(alts)];
  const r = alts.map((a) => evaluate1(c.want, a, (op && op.doc) || 0));
  const said = r.length === 1 ? r[0][1] : "any of " + JSON.stringify(r.map((x) => x[1]));
  return [r.every((x) => x[0]), said];
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
    const groups = [["main", s.checks, s.trace], ["extra", s.extra ? s.extra.checks : [], s.extra ? s.extra.trace : []]];
    for (const [which, checks, trace] of groups) for (const c of checks) {
      const [ok, said] = evaluate(c, (s._got?.[which] || [])[c.at], trace[c.at]);
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
