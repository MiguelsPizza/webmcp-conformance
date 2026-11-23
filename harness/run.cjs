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
const http = require("node:http");
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
    for (const k of ["id", "description", "status", "match"]) {
      if (!e[k]) throw new Error(`${file}: expectation ${e.id ?? "?"} has no ${k}`);
    }
    if (!e.issue && !e.spec) throw new Error(`${file}: ${e.id} has neither an issue nor a spec link`);
    if (e.match.actual) {
      new RegExp(e.match.actual);
      new RegExp(e.match.want ?? "");
    } else {
      if (!Array.isArray(e.match.rewrite) || !e.match.rewrite.length) throw new Error(`${file}: ${e.id} has no rewrites`);
      for (const r of e.match.rewrite) new RegExp(r.from, r.flags ?? "");
    }
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
  "returnEmpty", "returnNull", "returnNumber", "returnCyclic", "unregisterSelf", "unregisterSelf"];
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

// The frame tree the harness serves, in tree order; it must match `harnessDocs` in
// WebMCP/Model.lean. Origins 0-2 are served locally (ORIGINS below); origin 3 has no document.
const DOCS = [
  { origin: 0, parent: null, allow: false },
  { origin: 0, parent: 0, allow: false },
  { origin: 2, parent: 1, allow: true },
  { origin: 1, parent: 0, allow: true },
  { origin: 1, parent: 0, allow: false },
];
// Registration signals belong to the document that uses them: signal n lives in document n/3.
const SIGNALS_PER_DOC = 3;
const sameOrigin = (d) => DOCS.flatMap((x, i) => (x.origin === DOCS[d].origin ? [i] : []));
// In a multi-document trace, most operations still run in the top-level document.
const genDoc = (r) => choose(r, [[10, 0], [3, 1], [2, 2], [3, 3], [1, 4]]);
const genOrigins = (r, multi) => {
  if (r() < (multi ? 0.6 : 0.9)) return [];
  const n = 1 + Math.floor(r() * 2);
  return Array.from({ length: n }, () => choose(r, [[3, `origin:${Math.floor(r() * 4)}`],
    [1, `path:${Math.floor(r() * 3)}`], [0.3, "invalid"], [0.3, "insecure"]]));
};

function genTrace(r) {
  const ops = [];
  const len = 3 + Math.floor(r() * 12);
  // Half the traces stay in the top-level document, so single-document behaviour stays as well
  // covered as before frames were modelled; the other half spread over the frame tree.
  const multi = r() < 0.5;
  for (let i = 0; i < len; i++) {
    const k = r();
    const doc = multi ? genDoc(r) : 0;
    const signal = () => SIGNALS_PER_DOC * doc + Math.floor(r() * SIGNALS_PER_DOC);
    const input = () => {
      const n = Math.floor(r() * 10);
      return choose(r, [[8, `obj:${n}`], [1, "omitted"], [1, `fn:${n}`], [0.6, "toJSONNumber"],
        [0.6, "cyclic"]]);
    };
    if (k < 0.3) {
      ops.push({ op: "register", ...genTool(r), signal: r() < 0.5 ? signal() : null,
        exposedTo: genOrigins(r, multi), doc });
    } else if (k < 0.33) {
      ops.push({ op: "registerAbortSync", ...genTool(r), signal: signal(), exposedTo: genOrigins(r, multi), doc });
    } else if (k < 0.4) {
      ops.push({ op: "abort", signal: signal() });
    } else if (k < 0.58) {
      ops.push({ op: "getTools", fromOrigins: genOrigins(r, multi), doc });
    } else if (k < 0.88 || i < 3) {
      ops.push({ op: "execute", pending: true, input: input(), rc: r(), ri: r(), rd: r() });
    } else {
      // Calls started from one script and awaited together.
      const actions = [];
      const n = 2 + Math.floor(r() * 3);
      for (let j = 0; j < n; j++) {
        const a = r();
        if (a < 0.25) {
          actions.push({ act: "register", ...genTool(r), signal: r() < 0.6 ? signal() : null,
            exposedTo: genOrigins(r, multi) });
        } else if (a < 0.4) {
          actions.push({ act: "abort", signal: signal(), aim: r() });
        } else if (a < 0.55) {
          actions.push({ act: "getTools", fromOrigins: genOrigins(r, multi) });
        } else if (a < 0.9 || j === 0) {
          actions.push({ act: "execute", pending: true, input: input(), rc: r(), ri: r(),
            signal: choose(r, [[5, "none"], [3, "live"], [1, "aborted"]]) });
        } else {
          actions.push({ act: "cancel", target: Math.floor(r() * j) });
        }
      }
      ops.push({ op: "concurrent", actions, doc });
    }
  }
  return ops;
}

// Execute ops need a Tool that some earlier getTools() returned. The oracle's answers to the
// earlier operations say how many each getTools() call returned (the fewest, where the spec
// allows several outcomes; none for one in a `concurrent` operation), so each execute is
// resolved against the trace so far.
const toolCount = (o) => {
  if (o.startsWith("any:")) return Math.min(...JSON.parse(o.slice(4)).map(toolCount));
  if (!o.startsWith("tools:")) return 0;
  return o === "tools:" ? 0 : o.slice(6).split(";").length;
};
// The getTools() calls of `ops`, in order: how many Tools each surely returned, and which
// document made it.
function getToolsCalls(ops, outcomes) {
  const calls = [];
  ops.forEach((op, i) => {
    if (op.op === "getTools") calls.push({ size: toolCount(outcomes[i]), doc: op.doc ?? 0 });
    if (op.op === "concurrent") {
      for (const a of op.actions) if (a.act === "getTools") calls.push({ size: 0, doc: op.doc });
    }
  });
  return calls;
}
// Pick a Tool for a pending execute. The executing document is the one that made the
// getTools() call or one same-origin with it, which can reach the Tool through the other
// document's window; in a `concurrent` operation it is that operation's document.
function pickTool(p, calls, doc) {
  const avail = calls.map((c, i) => [c, i]).filter(([c]) => c.size > 0 &&
    (doc === undefined || DOCS[c.doc].origin === DOCS[doc].origin));
  if (!avail.length) return null;
  const [c, call] = avail[Math.floor(p.rc * avail.length)];
  return { call, index: Math.floor(p.ri * c.size), holder: c.doc };
}
function resolveOne(op, ops, outcomes) {
  const calls = getToolsCalls(ops, outcomes);
  if (op.op === "execute") {
    const t = pickTool(op, calls);
    if (!t) return null;
    const callers = sameOrigin(t.holder);
    const doc = op.rd < 0.7 ? t.holder : callers[Math.floor(((op.rd - 0.7) / 0.3) * callers.length)];
    return { op: "execute", call: t.call, index: t.index, input: op.input, doc };
  }
  // An execute with no Tool to use becomes an abort, so later actions keep their positions. Most
  // aborts after an execute aim at the signal its tool was registered with, so the races the
  // spec's notes discuss come up often.
  let aimed = null;
  const actions = op.actions.map((a) => {
    if (a.act === "abort") {
      const { aim, ...rest } = a;
      return aim < 0.6 && aimed != null ? { ...rest, signal: aimed } : rest;
    }
    if (a.act !== "execute") return a;
    const t = pickTool(a, calls, op.doc);
    if (!t) return { act: "abort", signal: SIGNALS_PER_DOC * op.doc };
    const sig = registeredSignal(ops, outcomes, t);
    if (sig != null && Math.floor(sig / SIGNALS_PER_DOC) === op.doc) aimed = sig;
    return { act: "execute", call: t.call, index: t.index, input: a.input, signal: a.signal };
  });
  return { ...op, actions };
}
// The registration signal of the tool a picked Tool most likely names: the last successful
// registration of that name in its source document.
function registeredSignal(ops, outcomes, t) {
  let k = -1;
  const i = ops.findIndex((o) => o.op === "getTools" && ++k === t.call);
  if (i < 0 || !outcomes[i].startsWith("tools:")) return null;
  const entry = outcomes[i].slice(6).split(";")[t.index];
  const name = entry.split("|")[0];
  const at = /@(\d+)/.exec(entry);
  const src = at ? Number(at[1]) : (ops[i].doc ?? 0);
  for (let j = i - 1; j >= 0; j--) {
    const o = ops[j];
    if (o.op === "register" && o.name === name && (o.doc ?? 0) === src && outcomes[j] === "ok") return o.signal;
  }
  return null;
}
const needsTool = (op) => op.op === "execute" || op.op === "concurrent";

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
    const ops = [];
    let known = [];
    for (const op of genTrace(r)) {
      if (!needsTool(op)) { ops.push(op); continue; }
      if (known.length !== ops.length) known = await ask(ops);
      const resolved = resolveOne(op, ops, known);
      if (resolved) ops.push(resolved);
    }
    traces.push({ ops, want: await ask(ops) });
  }
  return traces;
}

// --- the implementation, in the page ---------------------------------------------------
// Each document of the frame tree is served on its origin with `pageRunner` installed, and each
// operation runs in the document it names. Origin URLs are filled in by `serveFrames()`.
const ORIGINS = [];
let topUrl = null;

// Installed in every document as `window.__webmcpRun(op)`, which runs one operation there and
// returns its outcome string. State (signals, Tool objects) lives on the document's window.
function pageRunner(origins, docOrigins) {
  const mc = document.modelContext;
  const controllers = new Map();
  const controller = (n) => {
    if (!controllers.has(n)) controllers.set(n, new AbortController());
    return controllers.get(n);
  };
  // getTools() results by the index of the call in the trace, whichever document made it.
  const handles = (window.__webmcpHandles = new Map());
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
  const originArg = (a) => {
    const [k, n] = a.split(":");
    if (k === "origin") return origins[Number(n)];
    if (k === "path") return `${origins[Number(n)]}/some/path?q=1`;
    if (k === "invalid") return "not a url";
    return "http://example.com";
  };
  const tool = (op) => {
    const t = { name: op.name, execute: behaviors[op.behavior] };
    // Aborts the tool's own registration signal while it runs, then resolves with its input.
    if (op.behavior === "unregisterSelf") {
      t.execute = async (input) => {
        if (op.signal != null) controller(op.signal).abort();
        return input;
      };
    }
    if (op.title !== null) t.title = op.title;
    if (op.description !== null) t.description = op.description;
    if (op.inputSchema !== "absent") t.inputSchema = schemas[op.inputSchema]();
    if (op.outputSchema !== "absent") t.outputSchema = schemas[op.outputSchema]();
    if (op.annotations !== null) t.annotations = { ...op.annotations };
    return t;
  };
  const registerOptions = (op, signal) => {
    const options = signal == null ? {} : { signal };
    if (op.exposedTo !== undefined) options.exposedTo = op.exposedTo.map(originArg);
    return options;
  };
  // Every window of the frame tree, in tree order, so a Tool's `source` can be named by index.
  const windows = () => {
    const out = [];
    const walk = (w) => { out.push(w); for (let i = 0; i < w.length; i++) walk(w.frames[i]); };
    walk(window.top);
    return out;
  };
  // Only real TypeErrors and DOMExceptions count; anything else is reported as such.
  const errName = (e) =>
    e instanceof DOMException || e instanceof TypeError ? `err:${e.name}` : `err:non-standard:${e?.name}`;
  const json = (v) => (v === undefined ? "undefined" : JSON.stringify(v));
  const annotations = (a) =>
    a == null ? String(a) : JSON.stringify({ readOnlyHint: a.readOnlyHint,
      untrustedContentHint: a.untrustedContentHint, consequentialHint: a.consequentialHint,
      debugging: a.debugging });
  // `@<document>` when the Tool's source is another window. Operations that name a document
  // also check `origin` against that document's; older ones (no `doc`) don't, and a missing
  // `source` there counts as the caller's own.
  const view = (t, checkOrigin) => {
    const all = windows();
    const legacy = !checkOrigin && t.source === undefined;
    const src = legacy || t.source === window ? all.indexOf(window) : all.indexOf(t.source);
    let suffix = src === all.indexOf(window) ? "" : `@${src < 0 ? String(t.source) : src}`;
    if (checkOrigin && src >= 0 && t.origin !== origins[docOrigins[src]]) {
      suffix += `!origin=${String(t.origin)}`;
    }
    return [t.name, String(t.title), t.description, json(t.inputSchema), json(t.outputSchema),
      annotations(t.annotations)].join("|") + suffix;
  };
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
  const result = (r) => (typeof r === "string" ? `result:${r}` : `result-non-string:${String(r)}`);
  // The Tool, from whichever same-origin document's getTools() call returned it. (If the
  // implementation's getTools() rejected or returned fewer tools than the spec's, this is
  // undefined and the call fails with a TypeError.)
  const handle = (op) => (windows()[op.holder].__webmcpHandles.get(op.call) || [])[op.index];
  const getToolsOptions = (op) =>
    op.fromOrigins === undefined ? [] : [{ fromOrigins: op.fromOrigins.map(originArg) }];
  // Start every action of a `concurrent` operation from this one script, then await them all.
  // `settle` makes each call before its first await, so all calls start before any settles.
  const concurrent = async (op) => {
    const execSignals = new Map();
    const started = op.actions.map((a, i) => {
      if (a.act === "register") {
        const signal = a.signal == null ? null : controller(a.signal).signal;
        return settle(() => mc.registerTool(tool(a), registerOptions(a, signal)), done);
      } else if (a.act === "abort") {
        controller(a.signal).abort();
        return "ok";
      } else if (a.act === "getTools") {
        return settle(() => mc.getTools(...getToolsOptions(a)), (tools) => {
          handles.set(a.slot, tools);
          return "tools:" + tools.map((t) => view(t, true)).join(";");
        });
      } else if (a.act === "execute") {
        const options = {};
        if (a.signal !== "none") {
          const ac = new AbortController();
          if (a.signal === "aborted") ac.abort();
          execSignals.set(i, ac);
          options.signal = ac.signal;
        }
        const [input] = inputs(a.input);
        return settle(() => mc.executeTool(handle(a), input, options), result);
      }
      execSignals.get(a.target)?.abort();
      return "ok";
    });
    return "all:" + JSON.stringify(await Promise.all(started));
  };
  window.__webmcpRun = async (op) => {
    if (op.op === "concurrent") return concurrent(op);
    if (op.op === "register") {
      const signal = op.signal == null ? null : controller(op.signal).signal;
      return settle(() => mc.registerTool(tool(op), registerOptions(op, signal)), done);
    } else if (op.op === "registerAbortSync") {
      const ac = controller(op.signal);
      // Abort right after the call returns, before anything awaits its promise.
      const call = () => {
        try {
          return mc.registerTool(tool(op), registerOptions(op, ac.signal));
        } finally {
          ac.abort();
        }
      };
      return settle(call, done);
    } else if (op.op === "abort") {
      controller(op.signal).abort();
      return "ok";
    } else if (op.op === "getTools") {
      return settle(() => mc.getTools(...getToolsOptions(op)), (tools) => {
        handles.set(op.slot, tools);
        return "tools:" + tools.map((t) => view(t, op.doc !== undefined)).join(";");
      });
    } else {
      return settle(() => mc.executeTool(handle(op), ...inputs(op.input)), result);
    }
  };
}

// Serve every document of the frame tree, each on its own origin, with the polyfill (if any)
// and `pageRunner`. Origins 0 and 1 share a port and differ by host; origin 2 has another port.
async function serveFrames() {
  const page = (doc) => {
    const frames = DOCS.flatMap((d, i) => (d.parent === doc ? [i] : []))
      .map((i) => `<iframe src="${ORIGINS[DOCS[i].origin]}/doc/${i}"${DOCS[i].allow ? ' allow="tools"' : ""}></iframe>`);
    return `<!doctype html>${polyfill ? `<script>${polyfill}</script>` : ""}` +
      `<script>(${pageRunner})(${JSON.stringify([...ORIGINS, "https://other.example"])}, ` +
      `${JSON.stringify(DOCS.map((d) => d.origin))})</script>${frames.join("")}`;
  };
  const server = () => new Promise((res) => {
    const s = http.createServer((req, rsp) => {
      const m = /^\/doc\/(\d+)$/.exec(req.url);
      rsp.writeHead(m ? 200 : 404, { "content-type": "text/html" });
      rsp.end(m ? page(Number(m[1])) : "");
    });
    s.listen(0, "127.0.0.1", () => res(s));
  });
  const [a, b] = [await server(), await server()];
  ORIGINS.push(`http://127.0.0.1:${a.address().port}`, `http://localhost:${a.address().port}`,
    `http://127.0.0.1:${b.address().port}`);
  topUrl = `${ORIGINS[0]}/doc/0`;
  return [a, b];
}

// The Playwright frame of each document, by its URL.
function docFrames(page) {
  const byUrl = new Map(page.frames().map((f) => [f.url(), f]));
  return DOCS.map((d, i) => byUrl.get(`${ORIGINS[d.origin]}/doc/${i}`));
}

async function runInPage(page, ops) {
  await page.goto(topUrl);
  const frames = docFrames(page);
  const holders = [];
  const out = [];
  for (const op of ops) {
    const doc = op.op === "abort" ? Math.floor(op.signal / SIGNALS_PER_DOC) : (op.doc ?? 0);
    let arg = op;
    if (op.op === "getTools") {
      arg = { ...op, slot: holders.length };
      holders.push(doc);
    } else if (op.op === "execute") {
      arg = { ...op, holder: holders[op.call] };
    } else if (op.op === "concurrent") {
      // Each getTools() action takes the next call index; executes refer to earlier ones only.
      const before = holders.length;
      arg = { ...op, actions: op.actions.map((a) => {
        if (a.act === "execute") return { ...a, holder: holders[a.call] };
        if (a.act !== "getTools") return a;
        holders.push(doc);
        return { ...a, slot: holders.length - 1 };
      }) };
      if (arg.actions.some((a) => a.act === "execute" && a.call >= before)) throw new Error("bad trace");
    }
    out.push(await frames[doc].evaluate((a) => window.__webmcpRun(a), arg));
  }
  return out;
}

// --- comparison ------------------------------------------------------------------------
// Whether expectation e's conditions on the operation and the trace so far hold: every field in
// `where` equals the op's, and each `after` entry equals the fields of some earlier op, or of an
// action of an earlier `concurrent` op.
function conditionsHold(e, op, before) {
  const has = (o, fields) => Object.entries(fields).every(([k, v]) => o[k] === v);
  const m = e.match;
  if (m.where && !has(op, m.where)) return false;
  const seen = before.flatMap((o) => [o, ...(o.actions ?? [])]);
  return (m.after ?? []).every((c) => seen.some((o) => has(o, c)));
}
// The expectation that explains getting `got` where the model says `want`: its op matches, its
// conditions hold, and either applying its rewrites to want, in order, as
// String.prototype.replace(new RegExp(from, flags), to), gives exactly got, or (with `actual`)
// want matches the regex `want` and got the regex `actual`.
function expectedBy(op, want, got, before) {
  for (const e of expectations.active) {
    const m = e.match;
    if (![].concat(m.op).includes(op.op) || !conditionsHold(e, op, before)) continue;
    const rewrite = (w) => m.rewrite.reduce((x, r) => x.replace(new RegExp(r.from, r.flags ?? ""), r.to), w);
    if (m.actual ? new RegExp(m.want ?? "").test(want) && new RegExp(m.actual).test(got) : rewrite(want) === got) return e;
  }
  return null;
}
// Judge one outcome: null if `got` isn't allowed, else the expectations it took (none when it
// agrees). `any:[...]` allows any of the outcomes listed (taking the one needing the fewest
// expectations), and `all:[...]` judges a `concurrent` op's actions one by one, each as an op
// of its own kind in the concurrent op's document, marked `concurrent: true`.
function judge(op, want, got, before) {
  if (want === got) return [];
  if (want.startsWith("any:")) {
    let best = null;
    for (const w of JSON.parse(want.slice(4))) {
      const r = judge(op, w, got, before);
      if (r && (!best || r.length < best.length)) best = r;
    }
    return best;
  }
  if (want.startsWith("all:") && got.startsWith("all:")) {
    const [w, g] = [want, got].map((o) => JSON.parse(o.slice(4)));
    if (w.length !== g.length || w.length !== op.actions.length) return null;
    const { actions, ...rest } = op;
    const ids = [];
    for (let i = 0; i < w.length; i++) {
      const r = judge({ ...rest, ...actions[i], op: actions[i].act, concurrent: true }, w[i], g[i], before);
      if (!r) return null;
      ids.push(...r);
    }
    return ids;
  }
  const e = expectedBy(op, want, got, before);
  return e ? [e] : null;
}
// Compare one trace call by call. Expected divergences are tallied and the trace goes on, or, for
// an expectation with `stop` (one that leaves the states apart), ends without failing. The first
// unexpected one ends the comparison (bad is its index), since the model's state and the
// implementation's may differ from there on.
function compare(ops, want, got) {
  const r = { agree: 0, expected: {}, bad: -1, stopped: -1 };
  for (let i = 0; i < ops.length; i++) {
    const es = judge(ops[i], want[i], got[i], ops.slice(0, i));
    if (!es) {
      r.bad = i;
      break;
    }
    if (!es.length) {
      r.agree++;
      continue;
    }
    for (const e of es) r.expected[e.id] = (r.expected[e.id] || 0) + 1;
    if (es.some((e) => e.stop)) {
      r.stopped = i;
      break;
    }
  }
  return r;
}
const kindOf = (o) => (/^(tools|result|any|all):/.test(o) ? o.split(":")[0] : o);
// The first unexpected disagreement in a run, as a category such as "execute: spec err:X / impl result".
function mismatchKey(ops, want, got) {
  const { bad } = compare(ops, want, got);
  return bad < 0 ? null : `${ops[bad].op}: spec ${kindOf(want[bad])} / impl ${kindOf(got[bad])}`;
}

// Remove op i. Removing a getTools() (or a concurrent op with getTools() actions) also removes
// the executes that use its results, and renumbers later ones. A concurrent op that loses an
// execute goes as a whole, since its cancels refer to actions by position.
function removeAt(ops, i) {
  const calls = (o) => (o.op === "getTools" ? 1 : o.op === "concurrent" ? o.actions.filter((a) => a.act === "getTools").length : 0);
  const first = ops.slice(0, i).reduce((n, o) => n + calls(o), 0);
  const k = calls(ops[i]);
  if (!k) return ops.filter((_, j) => j !== i);
  const gone = (e) => e.call >= first && e.call < first + k;
  const fix = (e) => (e.call >= first + k ? { ...e, call: e.call - k } : e);
  return ops.flatMap((o, j) => {
    if (j === i) return [];
    if (o.op === "execute") return gone(o) ? [] : [fix(o)];
    if (o.op !== "concurrent") return [o];
    if (o.actions.some((a) => a.act === "execute" && gone(a))) return [];
    return [{ ...o, actions: o.actions.map((a) => (a.act === "execute" ? fix(a) : a)) }];
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
  const servers = await serveFrames();
  const page = await browser.newPage();
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
      counts.compared += c.stopped < 0 ? ops.length : c.stopped + 1;
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
  servers.forEach((s) => s.close());
  oracle?.stdin.end();
  process.exitCode = failures.size ? 1 : 0;
})();
