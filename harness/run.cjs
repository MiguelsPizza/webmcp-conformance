// Differential conformance test: random API-call traces run against a WebMCP implementation,
// compared call by call with what the Lean model (the oracle) says the spec requires.
//
//   node harness/run.cjs <target> [traces=300] [seed=1] [options]       live, needs the oracle
//   node harness/run.cjs <target> --replay <corpus.json> [options]       no Lean needed
//   node harness/run.cjs --record <corpus.json> [traces] [seed]          write a corpus
//
// <target> is one of:
//   polyfill:<path to dist/polyfill.js>   the polyfill, injected into Playwright's Chromium
//   chromium                              Chromium's native WebMCP (Blink feature flag)
//   chromium:<path to chrome binary>      the same, for another Chromium build
//
// options:
//   --results <file.json>        also write the run as machine-readable results (results/README.md)
//   --expectations <file.json>   expected divergences to use instead of expectations/<family>.json
//   --no-expectations            treat every divergence as unexpected
//
// A divergence an expectation describes (expectations/README.md) is counted under its id and the
// trace carries on; any other divergence ends the trace. The exit code is non-zero only if some
// trace had an unexpected divergence.
const { chromium } = require("playwright");
const { spawn, execFileSync } = require("node:child_process");
const fs = require("node:fs");
const path = require("node:path");
const readline = require("node:readline");

const root = path.join(__dirname, "..");
const specSha = JSON.parse(fs.readFileSync(path.join(root, "spec", "anchors.json"), "utf8")).spec;

const opts = { replay: null, record: null, results: null, expectations: null, noExpectations: false };
const positional = [];
for (let a = process.argv.slice(2); a.length; ) {
  const x = a.shift();
  if (x === "--no-expectations") opts.noExpectations = true;
  else if (/^--(replay|record|results|expectations)$/.test(x)) {
    if (!a.length) throw new Error(`${x} needs a file`);
    opts[x.slice(2)] = a.shift();
  } else if (x.startsWith("--")) throw new Error(`unknown option ${x}`);
  else positional.push(x);
}
const recordPath = opts.record;
const replayPath = opts.replay;
const target = recordPath ? "none" : positional[0];
if (!target) throw new Error("usage: node harness/run.cjs <target> [traces] [seed] | --replay <corpus> | --record <corpus>");
const [countArg = "300", seedArg = "1"] = recordPath ? positional : replayPath ? [] : positional.slice(1);
const [kind, ...rest] = target.split(":");
const targetArg = rest.join(":");
if (!recordPath && !["polyfill", "chromium"].includes(kind)) throw new Error(`unknown target ${target}`);
const polyfill = kind === "polyfill" ? fs.readFileSync(targetArg, "utf8") : "";
const launchOptions =
  kind === "chromium"
    ? { args: ["--enable-blink-features=WebMCP"], ...(targetArg ? { executablePath: targetArg } : {}) }
    : {};
const oraclePath = path.join(root, ".lake", "build", "bin", "oracle");

// --- what is being tested ----------------------------------------------------------------
const git = (dir, ...args) => {
  try {
    return execFileSync("git", ["-C", dir, ...args], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim();
  } catch {
    return null;
  }
};
// The polyfill's package.json version and its checkout's commit, when it has them.
function polyfillInfo(file) {
  const dir = path.dirname(path.resolve(file));
  let pkg = null;
  for (let d = dir; d !== path.dirname(d) && !pkg; d = path.dirname(d)) {
    const p = path.join(d, "package.json");
    if (fs.existsSync(p)) pkg = JSON.parse(fs.readFileSync(p, "utf8"));
  }
  return { path: shownPath(file), package: pkg?.name ?? null, version: pkg?.version ?? null,
    commit: git(dir, "rev-parse", "HEAD"), remote: git(dir, "remote", "get-url", "origin") };
}
// A local path as results files show it: relative to its git checkout, named after the
// checkout's folder, so the file doesn't carry the machine's own paths.
function shownPath(file) {
  const top = git(path.dirname(path.resolve(file)), "rev-parse", "--show-toplevel");
  return top ? path.join(path.basename(top), path.relative(top, path.resolve(file))) : path.basename(file);
}

// --- expected divergences ------------------------------------------------------------------
// Compare dotted version numbers: "<160" holds for 157.0.8103.78.
function versionMatches(range, version) {
  if (!range) return true;
  const m = /^(<=|>=|<|>|=)?\s*([\d.]+)$/.exec(range);
  if (!m || !version) return false;
  const a = version.split(".").map(Number);
  const b = m[2].split(".").map(Number);
  let c = 0;
  for (let i = 0; i < Math.max(a.length, b.length) && !c; i++) c = Math.sign((a[i] || 0) - (b[i] || 0));
  return { "<": c < 0, "<=": c <= 0, ">": c > 0, ">=": c >= 0, "=": c === 0 }[m[1] || "="];
}
function loadExpectations(version) {
  if (opts.noExpectations) return { file: null, active: [], skipped: [] };
  const file = opts.expectations ?? path.join(root, "expectations", `${kind}.json`);
  if (!fs.existsSync(file)) {
    if (opts.expectations) throw new Error(`no such expectations file ${file}`);
    return { file: null, active: [], skipped: [] };
  }
  const all = JSON.parse(fs.readFileSync(file, "utf8")).expectations;
  for (const e of all) {
    for (const k of ["id", "description", "issue", "status", "match"]) {
      if (!e[k]) throw new Error(`${file}: expectation ${e.id ?? "?"} has no ${k}`);
    }
    if (!Array.isArray(e.match.rewrite) || !e.match.rewrite.length) throw new Error(`${file}: ${e.id} has no rewrites`);
    for (const r of e.match.rewrite) new RegExp(r.from, r.flags ?? "");
  }
  const active = all.filter((e) => versionMatches(e.versions, version));
  return { file: path.relative(root, path.resolve(file)), active, skipped: all.filter((e) => !active.includes(e)) };
}
let expectations = { file: null, active: [], skipped: [] };

// --- trace generator -------------------------------------------------------------------
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const pick = (r, xs) => xs[Math.floor(r() * xs.length)];
// Weighted pick: [[weight, value], ...].
const choose = (r, pairs) => {
  let x = r() * pairs.reduce((n, [w]) => n + w, 0);
  for (const [w, v] of pairs) if ((x -= w) < 0) return v;
  return pairs[pairs.length - 1][1];
};

// A few names most of the time, so duplicates and re-registration happen often; edge cases
// for the name rule the rest of the time.
const COMMON_NAMES = ["a", "b", "c"];
const OTHER_NAMES = ["tool.x", "t-1", "B", "_", "123"];
const EDGE_NAMES = ["", "has space", "x".repeat(128), "x".repeat(129), "x".repeat(127) + "!",
  "ünï", "é", "Ａ", "ı", "a/b", "a\tb"];
const SCHEMAS = [[4, "absent"], [3, "object"], [1, "viaToJSON"], [0.4, "unserializable"], [0.3, "nonObject"]];
const BEHAVIORS = ["echo", "echo", "keys", "reject", "throwSync", "returnUndefined", "returnText",
  "returnEmpty", "returnNull", "returnNumber", "returnCyclic"];
const ANNOTATIONS = [[5, null], [1, {}], [1, { readOnlyHint: true }],
  [1, { consequentialHint: true, debugging: true }]];

function genTool(r) {
  return {
    name: choose(r, [[6, pick(r, COMMON_NAMES)], [2.5, pick(r, OTHER_NAMES)], [1.5, pick(r, EDGE_NAMES)]]),
    title: choose(r, [[5, null], [2, "T"], [1, ""], [1, "Tïtle"]]),
    description: choose(r, [[16, "d"], [1, ""], [0.5, null], [1, "Does a thing."]]),
    inputSchema: choose(r, SCHEMAS),
    outputSchema: choose(r, SCHEMAS),
    annotations: choose(r, ANNOTATIONS),
    behavior: pick(r, BEHAVIORS),
  };
}

function genTrace(r) {
  const ops = [];
  const len = 3 + Math.floor(r() * 12);
  for (let i = 0; i < len; i++) {
    const k = r();
    if (k < 0.35) {
      ops.push({ op: "register", ...genTool(r), signal: r() < 0.5 ? Math.floor(r() * 3) : null });
    } else if (k < 0.4) {
      ops.push({ op: "registerAbortSync", ...genTool(r), signal: Math.floor(r() * 3) });
    } else if (k < 0.5) {
      ops.push({ op: "abort", signal: Math.floor(r() * 3) });
    } else if (k < 0.67) {
      ops.push({ op: "getTools" });
    } else {
      const n = Math.floor(r() * 10);
      const input = choose(r, [[8, `obj:${n}`], [1, "omitted"], [1, `fn:${n}`],
        [0.6, "toJSONNumber"], [0.6, "cyclic"]]);
      ops.push({ op: "execute", pending: true, input, rc: r(), ri: r() });
    }
  }
  return ops;
}

// Execute ops need a Tool that some earlier getTools() returned. The oracle's answers to the
// getTools() calls say how many there were, so resolve them in a second pass.
const toolCount = (o) => (o === "tools:" ? 0 : o.slice(6).split(";").length);
function resolveExecutes(ops, outcomes) {
  const sizes = [];
  const out = [];
  ops.forEach((op, i) => {
    if (op.op === "getTools") sizes.push(outcomes[i] ? toolCount(outcomes[i]) : 0);
    if (op.op === "execute" && op.pending) {
      const avail = sizes.map((n, c) => [n, c]).filter(([n]) => n > 0);
      if (!avail.length) return;
      const [n, c] = avail[Math.floor(op.rc * avail.length)];
      out.push({ op: "execute", call: c, index: Math.floor(op.ri * n), input: op.input });
      return;
    }
    out.push(op);
  });
  return out;
}

// --- oracle ----------------------------------------------------------------------------
// Not started when replaying, so a recorded corpus runs without a Lean toolchain.
const oracle = replayPath ? null : spawn(oraclePath, [], { stdio: ["pipe", "pipe", "inherit"] });
const waiting = [];
if (oracle) {
  readline.createInterface({ input: oracle.stdout }).on("line", (l) => waiting.shift()(JSON.parse(l)));
  oracle.on("exit", (code) => {
    if (waiting.length) throw new Error(`oracle exited with ${code}`);
  });
}
const ask = async (ops) => {
  const want = await new Promise((res) => {
    waiting.push(res);
    oracle.stdin.write(JSON.stringify(ops) + "\n");
  });
  if (want.includes("invalid-request")) throw new Error(`harness bug: ${JSON.stringify(ops)}`);
  return want;
};

// Random traces with their execute ops resolved against the oracle's getTools() answers.
async function generate(count, seed) {
  const r = rng(seed);
  const traces = [];
  for (let t = 0; t < count; t++) {
    const raw = genTrace(r);
    const first = await ask(raw.filter((o) => o.op !== "execute"));
    let k = 0;
    const sized = raw.map((o) => (o.op === "execute" ? null : first[k++]));
    const ops = resolveExecutes(raw, sized);
    traces.push({ ops, want: await ask(ops) });
  }
  return traces;
}

// --- the implementation, in the page ---------------------------------------------------
async function runInPage(page, ops) {
  await page.goto("https://webmcp.test/");
  return page.evaluate(async (ops) => {
    const mc = document.modelContext;
    const controllers = new Map();
    const controller = (n) => {
      if (!controllers.has(n)) controllers.set(n, new AbortController());
      return controllers.get(n);
    };
    const cyclic = () => { const o = {}; o.self = o; return o; };
    const schemas = {
      object: () => ({ type: "object" }),
      viaToJSON: () => ({ toJSON() { return { type: "string" }; } }),
      unserializable: cyclic,
      nonObject: () => "x",
    };
    const behaviors = {
      echo: async (input) => input,
      keys: async (input) => Object.keys(input),
      reject: async () => { throw new Error("no"); },
      throwSync: () => { throw new Error("no"); },
      returnUndefined: async () => undefined,
      returnText: async () => "hi",
      returnEmpty: async () => "",
      returnNull: async () => null,
      returnNumber: async () => 5,
      returnCyclic: async () => cyclic(),
    };
    const inputs = (s) => {
      const [k, n] = s.split(":");
      if (k === "obj") return [{ n: Number(n) }];
      if (k === "fn") return [{ n: Number(n), f() {} }];
      if (k === "omitted") return [];
      if (k === "toJSONNumber") return [{ toJSON() { return 5; } }];
      return [cyclic()];
    };
    const tool = (op) => {
      const t = { name: op.name, execute: behaviors[op.behavior] };
      if (op.title !== null) t.title = op.title;
      if (op.description !== null) t.description = op.description;
      if (op.inputSchema !== "absent") t.inputSchema = schemas[op.inputSchema]();
      if (op.outputSchema !== "absent") t.outputSchema = schemas[op.outputSchema]();
      if (op.annotations !== null) t.annotations = { ...op.annotations };
      return t;
    };
    // Only real TypeErrors and DOMExceptions count; anything else is reported as such.
    const errName = (e) =>
      e instanceof DOMException || e instanceof TypeError ? `err:${e.name}` : `err:non-standard:${e?.name}`;
    const json = (v) => (v === undefined ? "undefined" : JSON.stringify(v));
    const annotations = (a) =>
      a == null ? String(a) : JSON.stringify({ readOnlyHint: a.readOnlyHint,
        untrustedContentHint: a.untrustedContentHint, consequentialHint: a.consequentialHint,
        debugging: a.debugging });
    const view = (t) => [t.name, String(t.title), t.description, json(t.inputSchema),
      json(t.outputSchema), annotations(t.annotations)].join("|");
    // A promise-returning method must return a promise, never throw; settle it with a timeout.
    const settle = async (call, onValue) => {
      let p;
      try { p = call(); } catch (e) { return `threw:${errName(e)}`; }
      if (!(p instanceof Promise)) return "not-a-promise";
      let timer;
      const timeout = new Promise((_, rej) => { timer = setTimeout(() => rej("timeout"), 5000); });
      try {
        return onValue(await Promise.race([p, timeout]));
      } catch (e) {
        return e === "timeout" ? "timeout" : errName(e);
      } finally {
        clearTimeout(timer);
      }
    };
    const done = (v) => (v === undefined ? "ok" : `fulfilled:${String(v)}`);
    const handles = [];
    const out = [];
    for (const op of ops) {
      if (op.op === "register") {
        const options = op.signal == null ? {} : { signal: controller(op.signal).signal };
        out.push(await settle(() => mc.registerTool(tool(op), options), done));
      } else if (op.op === "registerAbortSync") {
        const ac = controller(op.signal);
        // Abort right after the call returns, before anything awaits its promise.
        const call = () => {
          try {
            return mc.registerTool(tool(op), { signal: ac.signal });
          } finally {
            ac.abort();
          }
        };
        out.push(await settle(call, done));
      } else if (op.op === "abort") {
        controller(op.signal).abort();
        out.push("ok");
      } else if (op.op === "getTools") {
        out.push(await settle(() => mc.getTools(), (tools) => {
          handles.push(tools);
          return "tools:" + tools.map(view).join(";");
        }));
      } else {
        const t = handles[op.call][op.index];
        out.push(await settle(() => mc.executeTool(t, ...inputs(op.input)),
          (r) => (typeof r === "string" ? `result:${r}` : `result-non-string:${String(r)}`)));
      }
    }
    return out;
  }, ops);
}

// --- comparison ------------------------------------------------------------------------
// The id of the expectation that explains getting `got` where the model says `want`: its op
// matches, and applying its rewrites to want, in order, as String.prototype.replace(new
// RegExp(from, flags), to), gives exactly got.
function expectedBy(op, want, got) {
  for (const e of expectations.active) {
    const m = e.match;
    if (![].concat(m.op).includes(op.op)) continue;
    const rewritten = m.rewrite.reduce((s, r) => s.replace(new RegExp(r.from, r.flags ?? ""), r.to), want);
    if (rewritten === got) return e.id;
  }
  return null;
}
// Compare one trace call by call. Expected divergences are tallied and the trace goes on. The
// first unexpected one ends the comparison (bad is its index), since the model's state and the
// implementation's may differ from there on.
function compare(ops, want, got) {
  const r = { agree: 0, expected: {}, bad: -1 };
  for (let i = 0; i < ops.length; i++) {
    if (want[i] === got[i]) {
      r.agree++;
      continue;
    }
    const id = expectedBy(ops[i], want[i], got[i]);
    if (!id) {
      r.bad = i;
      break;
    }
    r.expected[id] = (r.expected[id] || 0) + 1;
  }
  return r;
}
const kindOf = (o) => (/^(tools|result):/.test(o) ? o.split(":")[0] : o);
// The first unexpected disagreement in a run, as a category such as "execute: spec err:X / impl result".
function mismatchKey(ops, want, got) {
  const { bad } = compare(ops, want, got);
  return bad < 0 ? null : `${ops[bad].op}: spec ${kindOf(want[bad])} / impl ${kindOf(got[bad])}`;
}

// Remove op i. Removing a getTools() also removes the executes that use it and renumbers later ones.
function removeAt(ops, i) {
  if (ops[i].op !== "getTools") return ops.filter((_, j) => j !== i);
  const g = ops.slice(0, i).filter((o) => o.op === "getTools").length;
  return ops.flatMap((o, j) => {
    if (j === i || (o.op === "execute" && o.call === g)) return [];
    return o.op === "execute" && o.call > g ? [{ ...o, call: o.call - 1 }] : [o];
  });
}

// Shrink a failing trace by removing ops while it still fails the same way. A removal that
// leaves an execute pointing past the tools its getTools() now returns is skipped.
async function shrink(page, ops, key) {
  let cur = ops;
  for (let changed = true; changed; ) {
    changed = false;
    for (let i = 0; i < cur.length; i++) {
      const cand = removeAt(cur, i);
      let want;
      try { want = await ask(cand); } catch { continue; }
      const got = await runInPage(page, cand);
      if (mismatchKey(cand, want, got) === key) { cur = cand; changed = true; break; }
    }
  }
  return cur;
}

function printMismatch(key, f, label) {
  console.log(`\nMISMATCH ${key} (first unexpected divergence in ${f.traces} traces)\n  ${label}:`);
  f.ops.forEach((o, i) => console.log(`   ${JSON.stringify(o)}\n      spec: ${f.want[i]}\n      impl: ${f.got[i]}`));
}

// How often each kind of outcome occurs per op, so gaps in what the corpus exercises show.
function coverage(traces) {
  const counts = new Map();
  for (const { ops, want } of traces) {
    ops.forEach((o, i) => {
      const k = `${o.op.padEnd(18)} ${want[i] === "tools:" ? "tools (empty)" : kindOf(want[i])}`;
      counts.set(k, (counts.get(k) || 0) + 1);
    });
  }
  return [...counts].sort().map(([k, n]) => `  ${k.padEnd(48)} ${n}`).join("\n");
}

(async () => {
  if (recordPath) {
    const traces = await generate(Number(countArg), Number(seedArg));
    fs.writeFileSync(recordPath, JSON.stringify({ spec: specSha, seed: Number(seedArg), traces }) + "\n");
    console.log(`recorded ${traces.length} traces to ${recordPath}\n\noutcomes per op:\n${coverage(traces)}`);
    oracle.stdin.end();
    return;
  }
  const browser = await chromium.launch(launchOptions);
  const browserVersion = browser.version();
  const implementation =
    kind === "polyfill"
      ? { kind, ...polyfillInfo(targetArg) }
      : { kind, executable: targetArg || "playwright-bundled", version: browserVersion };
  expectations = loadExpectations(implementation.version);
  console.log(`target ${target}, browser ${browserVersion}` +
    (kind === "polyfill" ? `, polyfill ${implementation.version ?? "?"} at ${implementation.commit?.slice(0, 7) ?? "?"}` : ""));
  console.log(expectations.file
    ? `expectations ${expectations.file}: ${expectations.active.length} apply` +
      (expectations.skipped.length ? `, ${expectations.skipped.length} not for this version` : "")
    : "no expectations: every divergence counts as unexpected");
  const page = await browser.newPage();
  await page.route("https://webmcp.test/", (route) =>
    route.fulfill({ contentType: "text/html", body: `<!doctype html>${polyfill ? `<script>${polyfill}</script>` : ""}` }));
  const corpus = replayPath ? JSON.parse(fs.readFileSync(replayPath, "utf8")) : null;
  if (corpus && corpus.spec !== specSha) console.log(`warning: corpus is for spec ${corpus.spec}, model is at ${specSha}`);
  const traces = corpus ? corpus.traces : await generate(Number(countArg), Number(seedArg));
  // Per mismatch category: how many traces hit it first, and the shrunk trace (live) or the
  // shortest failing trace cut after the divergence (replay).
  const failures = new Map();
  const counts = { traces: traces.length, calls: 0, compared: 0, agree: 0,
    expected: Object.fromEntries(expectations.active.map((e) => [e.id, 0])), unexpected: 0 };
  for (const { ops, want } of traces) {
    const got = await runInPage(page, ops);
    const c = compare(ops, want, got);
    counts.calls += ops.length;
    counts.agree += c.agree;
    for (const [id, n] of Object.entries(c.expected)) counts.expected[id] += n;
    if (c.bad < 0) {
      counts.compared += ops.length;
      continue;
    }
    counts.compared += c.bad + 1;
    counts.unexpected++;
    const key = mismatchKey(ops, want, got);
    const prev = failures.get(key);
    if (replayPath) {
      const end = c.bad + 1;
      const f = { traces: (prev?.traces ?? 0) + 1, ops: ops.slice(0, end), want: want.slice(0, end), got: got.slice(0, end) };
      failures.set(key, !prev || f.ops.length < prev.ops.length ? f : { ...prev, traces: f.traces });
    } else if (prev) {
      prev.traces++;
    } else {
      const small = await shrink(page, ops, key);
      failures.set(key, { traces: 1, ops: small, want: await ask(small), got: await runInPage(page, small) });
    }
  }
  console.log(`${counts.traces} traces, ${counts.calls} operations, ${counts.compared} compared: ` +
    `${counts.agree} agree, ${counts.compared - counts.agree - counts.unexpected} expected divergences, ` +
    `${counts.unexpected} unexpected`);
  for (const [id, n] of Object.entries(counts.expected)) if (n) console.log(`  expected ${String(n).padStart(5)}  ${id}`);
  if (!failures.size) console.log("no unexpected divergences");
  for (const [key, f] of failures) printMismatch(key, f, replayPath ? "shortest failing trace" : "minimal trace");
  if (opts.results) {
    const results = {
      target: kind === "polyfill" ? `polyfill:${implementation.path}` : target,
      implementation,
      browser: { name: "chromium", version: browserVersion, playwright: require("playwright/package.json").version },
      spec: specSha,
      corpus: corpus
        ? { file: path.relative(root, path.resolve(replayPath)), spec: corpus.spec, seed: corpus.seed ?? null, traces: traces.length }
        : { generated: true, seed: Number(seedArg), traces: traces.length },
      date: new Date().toISOString(),
      expectations: expectations.file
        ? { file: expectations.file, applied: expectations.active.map((e) => e.id), skipped: expectations.skipped.map((e) => e.id) }
        : null,
      counts,
      unexpected: [...failures].map(([key, f]) => ({
        key, traces: f.traces, trace: f.ops.map((op, i) => ({ op, model: f.want[i], actual: f.got[i] })),
      })),
    };
    fs.mkdirSync(path.dirname(path.resolve(opts.results)), { recursive: true });
    fs.writeFileSync(opts.results, JSON.stringify(results, null, 2) + "\n");
    console.log(`wrote ${opts.results}`);
  }
  await browser.close();
  oracle?.stdin.end();
  process.exitCode = failures.size ? 1 : 0;
})();
