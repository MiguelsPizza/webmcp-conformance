// Differential conformance test: random API-call traces run against a WebMCP implementation,
// compared call by call with what the Lean model (the oracle) says the spec requires.
//
//   node harness/run.cjs <target> [traces=300] [seed=1] [--known]       live, needs the oracle
//   node harness/run.cjs <target> --replay <corpus.json> [--known]       no Lean needed
//   node harness/run.cjs --record <corpus.json> [traces] [seed]          write a corpus
//
// <target> is one of:
//   polyfill:<path to dist/polyfill.js>   the polyfill, injected into Playwright's Chromium
//   chromium                              Chromium's native WebMCP (Blink feature flag)
//   chromium:<path to chrome binary>      the same, for another Chromium build
//
// --known treats the result-serialization differences tracked in spec issue #361 as equal (and
// counts them), so they don't hide other bugs later in the same trace.
const { chromium } = require("playwright");
const { spawn } = require("node:child_process");
const fs = require("node:fs");
const http = require("node:http");
const path = require("node:path");
const readline = require("node:readline");

const root = path.join(__dirname, "..");
const specSha = JSON.parse(fs.readFileSync(path.join(root, "spec", "anchors.json"), "utf8")).spec;
const flags = new Set(process.argv.slice(2).filter((a) => a === "--known"));
const argv = process.argv.slice(2).filter((a) => !flags.has(a));
const recordPath = argv[0] === "--record" ? argv[1] : null;
const replayPath = argv[1] === "--replay" ? argv[2] : null;
const target = recordPath ? "none" : argv[0];
const [countArg = "300", seedArg = "1"] = recordPath ? argv.slice(2) : replayPath ? [] : argv.slice(1);
const [kind, ...rest] = target.split(":");
const targetArg = rest.join(":");
const polyfill = kind === "polyfill" ? fs.readFileSync(targetArg, "utf8") : "";
const launchOptions =
  kind === "chromium"
    ? { args: ["--enable-blink-features=WebMCP"], ...(targetArg ? { executablePath: targetArg } : {}) }
    : {};
const oraclePath = path.join(root, ".lake", "build", "bin", "oracle");

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
// Most operations run in the top-level document, so single-document behaviour stays well covered.
const genDoc = (r) => choose(r, [[10, 0], [3, 1], [2, 2], [3, 3], [1, 4]]);
const genOrigins = (r) => {
  if (r() < 0.6) return [];
  const n = 1 + Math.floor(r() * 2);
  return Array.from({ length: n }, () => choose(r, [[3, `origin:${Math.floor(r() * 4)}`],
    [1, `path:${Math.floor(r() * 3)}`], [0.3, "invalid"], [0.3, "insecure"]]));
};

function genTrace(r) {
  const ops = [];
  const len = 3 + Math.floor(r() * 12);
  for (let i = 0; i < len; i++) {
    const k = r();
    const doc = genDoc(r);
    const signal = () => SIGNALS_PER_DOC * doc + Math.floor(r() * SIGNALS_PER_DOC);
    const input = () => {
      const n = Math.floor(r() * 10);
      return choose(r, [[8, `obj:${n}`], [1, "omitted"], [1, `fn:${n}`], [0.6, "toJSONNumber"],
        [0.6, "cyclic"]]);
    };
    if (k < 0.3) {
      ops.push({ op: "register", ...genTool(r), signal: r() < 0.5 ? signal() : null,
        exposedTo: genOrigins(r), doc });
    } else if (k < 0.33) {
      ops.push({ op: "registerAbortSync", ...genTool(r), signal: signal(), exposedTo: genOrigins(r), doc });
    } else if (k < 0.4) {
      ops.push({ op: "abort", signal: signal() });
    } else if (k < 0.58) {
      ops.push({ op: "getTools", fromOrigins: genOrigins(r), doc });
    } else if (k < 0.8 || i < 3) {
      ops.push({ op: "execute", pending: true, input: input(), rc: r(), ri: r(), rd: r() });
    } else {
      // Calls started from one script and awaited together.
      const actions = [];
      const n = 2 + Math.floor(r() * 3);
      for (let j = 0; j < n; j++) {
        const a = r();
        if (a < 0.25) {
          actions.push({ act: "register", ...genTool(r), signal: r() < 0.6 ? signal() : null,
            exposedTo: genOrigins(r) });
        } else if (a < 0.45) {
          actions.push({ act: "abort", signal: signal(), aim: r() });
        } else if (a < 0.55) {
          actions.push({ act: "getTools", fromOrigins: genOrigins(r) });
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
// Differences spec issue #361 tracks: Chromium stringifies primitive results instead of
// JSON-encoding them, and turns undefined and "" into strings.
function known361(want, got) {
  if (/^result:".*"$/.test(want) && got === `result:${want.slice(8, -1)}`) return true;
  if (want === 'result:""' && got === "result:Operation succeeded") return true;
  if (want === "err:OperationError" && got === "result:undefined") return true;
  return false;
}
// `any:[...]` accepts any of the outcomes listed, and `all:[...]` compares the outcomes of a
// `concurrent` operation's actions one by one.
const same = (want, got, stats) => {
  if (want === got) return true;
  if (want.startsWith("any:")) return JSON.parse(want.slice(4)).some((w) => same(w, got, stats));
  if (want.startsWith("all:") && got.startsWith("all:")) {
    const [w, g] = [want, got].map((o) => JSON.parse(o.slice(4)));
    return w.length === g.length && w.every((x, i) => same(x, g[i], stats));
  }
  if (flags.has("--known") && known361(want, got)) {
    if (stats) stats.known361++;
    return true;
  }
  return false;
};
const kindOf = (o) => (/^(tools|result|any|all):/.test(o) ? o.split(":")[0] : o);
// The first disagreement in a run, as a category such as "execute: spec err:X / impl result".
function mismatchKey(ops, want, got, stats) {
  const bad = got.findIndex((g, i) => !same(want[i], g, stats));
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
  console.log(`\nMISMATCH ${key}\n  ${label}:`);
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
  console.log(`target ${target}, browser ${browser.version()}`);
  const servers = await serveFrames();
  const page = await browser.newPage();
  const corpus = replayPath ? JSON.parse(fs.readFileSync(replayPath, "utf8")) : null;
  if (corpus && corpus.spec !== specSha) console.log(`warning: corpus is for spec ${corpus.spec}, model is at ${specSha}`);
  const traces = corpus ? corpus.traces : await generate(Number(countArg), Number(seedArg));
  // Per mismatch category: the shrunk trace (live) or the shortest failing trace (replay).
  const failures = new Map();
  const stats = { known361: 0 };
  let opsRun = 0;
  for (const { ops, want } of traces) {
    const got = await runInPage(page, ops);
    opsRun += ops.length;
    const key = mismatchKey(ops, want, got, stats);
    if (!key) continue;
    if (replayPath) {
      // Keep the trace up to its first disagreement.
      const end = got.findIndex((g, i) => !same(want[i], g)) + 1;
      const f = { ops: ops.slice(0, end), want: want.slice(0, end), got: got.slice(0, end) };
      const prev = failures.get(key);
      if (!prev || f.ops.length < prev.ops.length) failures.set(key, f);
    } else if (!failures.has(key)) {
      const small = await shrink(page, ops, key);
      failures.set(key, { ops: small, want: await ask(small), got: await runInPage(page, small) });
    }
  }
  console.log(`${traces.length} traces, ${opsRun} operations`);
  if (flags.has("--known")) console.log(`${stats.known361} results differed only as spec issue #361 describes`);
  if (!failures.size) console.log("implementation agrees with the model on every operation");
  for (const [key, f] of failures) printMismatch(key, f, replayPath ? "shortest failing trace" : "minimal trace");
  await browser.close();
  servers.forEach((s) => s.close());
  oracle?.stdin.end();
  process.exitCode = failures.size ? 1 : 0;
})();
