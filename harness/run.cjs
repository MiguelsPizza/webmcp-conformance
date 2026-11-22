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
// Differences spec issue #361 tracks: Chromium stringifies primitive results instead of
// JSON-encoding them, and turns undefined and "" into strings.
function known361(want, got) {
  if (/^result:".*"$/.test(want) && got === `result:${want.slice(8, -1)}`) return true;
  if (want === 'result:""' && got === "result:Operation succeeded") return true;
  if (want === "err:OperationError" && got === "result:undefined") return true;
  return false;
}
const same = (want, got, stats) => {
  if (want === got) return true;
  if (flags.has("--known") && known361(want, got)) {
    if (stats) stats.known361++;
    return true;
  }
  return false;
};
const kindOf = (o) => (/^(tools|result):/.test(o) ? o.split(":")[0] : o);
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
  const page = await browser.newPage();
  await page.route("https://webmcp.test/", (route) =>
    route.fulfill({ contentType: "text/html", body: `<!doctype html>${polyfill ? `<script>${polyfill}</script>` : ""}` }));
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
  oracle?.stdin.end();
  process.exitCode = failures.size ? 1 : 0;
})();
