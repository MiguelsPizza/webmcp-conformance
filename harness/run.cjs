// Differential conformance test: random API-call traces run against a WebMCP implementation,
// compared op by op with what the Lean model (the oracle) says the spec requires.
//
//   node harness/run.cjs <target> [traces=300] [seed=1]
//
// <target> is one of:
//   polyfill:<path to dist/polyfill.js>   the polyfill, injected into stock Chromium
//   chromium                              Chromium's native WebMCP (Blink feature flag)
//   chromium:<path to chrome binary>      the same, for another Chromium build
const { chromium } = require("playwright");
const { spawn } = require("node:child_process");
const fs = require("node:fs");
const path = require("node:path");
const readline = require("node:readline");

const [target, countArg = "300", seedArg = "1"] = process.argv.slice(2);
const [kind, ...rest] = target.split(":");
const targetArg = rest.join(":");
const polyfill = kind === "polyfill" ? fs.readFileSync(targetArg, "utf8") : "";
const launchOptions =
  kind === "chromium"
    ? { args: ["--enable-blink-features=WebMCP"], ...(targetArg ? { executablePath: targetArg } : {}) }
    : {};
const oraclePath = path.join(__dirname, "..", ".lake", "build", "bin", "oracle");

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
const NAMES = ["a", "b", "c", "tool.x", "t-1", "B", "_", "", "has space", "x".repeat(128),
  "x".repeat(129), "ünï", "a/b"];
const pick = (r, xs) => xs[Math.floor(r() * xs.length)];

function genTrace(r) {
  const ops = [];
  const len = 3 + Math.floor(r() * 12);
  for (let i = 0; i < len; i++) {
    const k = r();
    if (k < 0.45) {
      ops.push({
        op: "register",
        // Mostly a few names, so re-registration and duplicates happen often.
        name: r() < 0.6 ? pick(r, NAMES.slice(0, 3)) : r() < 0.85 ? pick(r, NAMES.slice(0, 7)) : pick(r, NAMES),
        description: r() < 0.93 ? "d" : "",
        inputSchema: pick(r, ["absent", "absent", "ok", "ok", "unserializable"].slice(0, r() < 0.9 ? 4 : 5)),
        outputSchema: pick(r, ["absent", "absent", "ok", "ok", "unserializable"].slice(0, r() < 0.93 ? 4 : 5)),
        behavior: pick(r, ["echo", "echo", "echo", "reject", "throwSync", "returnUndefined", "returnText", "returnEmpty"]),
        signal: r() < 0.5 ? Math.floor(r() * 3) : null,
      });
    } else if (k < 0.6) {
      ops.push({ op: "abort", signal: Math.floor(r() * 3) });
    } else if (k < 0.78) {
      ops.push({ op: "getTools" });
    } else {
      ops.push({ op: "execute", pending: true, input: r() < 0.92 ? Math.floor(r() * 10) : null,
        rc: r(), ri: r() });
    }
  }
  return ops;
}

// Execute ops need a Tool that some earlier getTools() returned. The oracle's own answers to the
// getTools() calls tell us how many there were, so resolve them in a second pass.
function resolveExecutes(ops, outcomes) {
  const sizes = [];
  const out = [];
  ops.forEach((op, i) => {
    if (op.op === "getTools") {
      const o = outcomes ? outcomes[i] : null;
      sizes.push(o ? (o === "tools:" ? 0 : o.slice(6).split(",").length) : 0);
    }
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
const oracle = spawn(oraclePath, [], { stdio: ["pipe", "pipe", "inherit"] });
const oracleLines = readline.createInterface({ input: oracle.stdout });
const waiting = [];
oracleLines.on("line", (l) => waiting.shift()(JSON.parse(l)));
const ask = (ops) => new Promise((res) => { waiting.push(res); oracle.stdin.write(JSON.stringify(ops) + "\n"); });

// --- the implementation, in the page -------------------------------------------------------------
async function runInPage(page, ops) {
  await page.goto("https://webmcp.test/");
  return page.evaluate(async (ops) => {
    const controllers = new Map();
    const signal = (n) => {
      if (!controllers.has(n)) controllers.set(n, new AbortController());
      return controllers.get(n);
    };
    const cyclic = () => { const o = {}; o.self = o; return o; };
    const schema = (s) => (s === "ok" ? { type: "object" } : s === "unserializable" ? cyclic() : undefined);
    const behaviors = {
      echo: async (input) => input,
      reject: async () => { throw new Error("no"); },
      throwSync: () => { throw new Error("no"); },
      returnUndefined: async () => undefined,
      returnText: async () => "hi",
      returnEmpty: async () => "",
    };
    const handles = [];
    const out = [];
    for (const op of ops) {
      try {
        if (op.op === "register") {
          const tool = { name: op.name, description: op.description, execute: behaviors[op.behavior] };
          if (op.inputSchema !== "absent") tool.inputSchema = schema(op.inputSchema);
          if (op.outputSchema !== "absent") tool.outputSchema = schema(op.outputSchema);
          const options = op.signal == null ? {} : { signal: signal(op.signal).signal };
          await document.modelContext.registerTool(tool, options);
          out.push("ok");
        } else if (op.op === "abort") {
          signal(op.signal).abort();
          out.push("ok");
        } else if (op.op === "getTools") {
          const tools = await document.modelContext.getTools();
          handles.push(tools);
          out.push("tools:" + tools.map((t) => t.name).join(","));
        } else {
          const input = op.input == null ? cyclic() : { n: op.input };
          const r = await document.modelContext.executeTool(handles[op.call][op.index], input);
          out.push("result:" + r);
        }
      } catch (e) {
        out.push("err:" + e.name);
      }
    }
    return out;
  }, ops);
}

const kindOf = (o) => (/^(tools|result):/.test(o) ? o.split(":")[0] : o);
// The first disagreement in a run, as a category such as "execute: spec err:X / impl result".
function mismatchKey(ops, want, got) {
  const bad = got.findIndex((g, i) => g !== want[i]);
  return bad < 0 ? null : `${ops[bad].op}: spec ${kindOf(want[bad])} / impl ${kindOf(got[bad])}`;
}

// Shrink a failing trace by dropping ops while it still fails the same way.
async function shrink(page, ops, key) {
  let cur = ops;
  for (let changed = true; changed; ) {
    changed = false;
    for (let i = 0; i < cur.length; i++) {
      const cand = cur.filter((_, j) => j !== i);
      if (cand.some((o, j) => o.op === "execute" && cand.slice(0, j).filter((p) => p.op === "getTools").length <= o.call)) continue;
      const want = await ask(cand);
      const cmp = (o) => o.op !== "execute" || want[cand.indexOf(o)] !== "ok";
      if (!cand.every(cmp)) continue;
      const got = await runInPage(page, cand);
      if (mismatchKey(cand, want, got) === key) { cur = cand; changed = true; break; }
    }
  }
  return cur;
}

(async () => {
  const browser = await chromium.launch(launchOptions);
  console.log(`target ${target}, browser ${browser.version()}`);
  const page = await browser.newPage();
  await page.route("https://webmcp.test/", (route) =>
    route.fulfill({ contentType: "text/html", body: `<!doctype html>${polyfill ? `<script>${polyfill}</script>` : ""}` }));
  const r = rng(Number(seedArg));
  const failures = new Map();
  let opsRun = 0;
  for (let t = 0; t < Number(countArg); t++) {
    const raw = genTrace(r);
    // First pass fixes which getTools() calls exist; the oracle then sizes them.
    const firstPass = await ask(resolveExecutes(raw, null).filter((o) => o.op !== "execute"));
    const sizedOutcomes = [];
    let k = 0;
    for (const o of raw) sizedOutcomes.push(o.op === "execute" ? null : firstPass[k++]);
    const ops = resolveExecutes(raw, sizedOutcomes);
    const want = await ask(ops);
    const got = await runInPage(page, ops);
    opsRun += ops.length;
    const key = mismatchKey(ops, want, got);
    if (key && !failures.has(key)) failures.set(key, await shrink(page, ops, key));
  }
  console.log(`${countArg} traces, ${opsRun} operations`);
  if (!failures.size) console.log("implementation agrees with the model on every operation");
  for (const [key, ops] of failures) {
    const want = await ask(ops);
    const got = await runInPage(page, ops);
    console.log(`\nMISMATCH ${key}\n  minimal trace:`);
    ops.forEach((o, i) => console.log(`   ${JSON.stringify(o)}\n      spec: ${want[i]}   impl: ${got[i]}`));
  }
  await browser.close();
  oracle.stdin.end();
  process.exitCode = failures.size ? 1 : 0;
})();
