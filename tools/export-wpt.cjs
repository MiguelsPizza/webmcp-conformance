// Turn recorded traces into web-platform-tests testharness.js tests, with the outcomes the
// model gives (asked of the oracle, so `lake build oracle` first).
//
//   node tools/export-wpt.cjs <trace file>... [--out <dir>] [--trace <n>] [--focus]
//
// A trace file is in the corpus format (corpus/README.md): a repro or a corpus. Each trace
// becomes one <basename>[-<n>].https.html in <dir> (default wpt-export/), holding one
// promise_test that makes the trace's calls in order and asserts the model's outcome for each.
// The tests use document.modelContext directly, as the WPT webmcp/imperative tests do.
//
// --focus asserts every member of a Tool only for the trace's last call: earlier getTools()
// calls check just the names, so a test about the last call doesn't fail on an unrelated member.
const { execFileSync } = require("node:child_process");
const fs = require("node:fs");
const path = require("node:path");

const root = path.join(__dirname, "..");
const specSha = JSON.parse(fs.readFileSync(path.join(root, "spec", "anchors.json"), "utf8")).spec;
const oraclePath = path.join(root, ".lake", "build", "bin", "oracle");

const args = process.argv.slice(2);
let out = path.join(root, "wpt-export");
let only = null;
let focus = false;
const inputs = [];
while (args.length) {
  const a = args.shift();
  if (a === "--out") out = args.shift();
  else if (a === "--trace") only = Number(args.shift());
  else if (a === "--focus") focus = true;
  else inputs.push(a);
}
if (!inputs.length) throw new Error("usage: node tools/export-wpt.cjs <trace file>... [--out <dir>] [--trace <n>]");

const oracle = (ops) => JSON.parse(execFileSync(oraclePath, { input: JSON.stringify(ops) + "\n", encoding: "utf8" }));
const js = (v) => JSON.stringify(v).replace(/[\u007f-￿]/g, (c) => `\\u${c.charCodeAt(0).toString(16).padStart(4, "0")}`);
const html = (s) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

// The same author-supplied values the harness uses (harness/run.cjs, runInPage).
const SCHEMAS = {
  object: "{ type: 'object' }",
  viaToJSON: "{ toJSON() { return { type: 'string' }; } }",
  unserializable: "cyclic()",
  nonObject: "'x'",
};
const BEHAVIORS = {
  echo: "async (input) => input",
  keys: "async (input) => Object.keys(input)",
  reject: "async () => { throw new Error('no'); }",
  throwSync: "() => { throw new Error('no'); }",
  returnUndefined: "async () => undefined",
  returnText: "async () => 'hi'",
  returnEmpty: "async () => ''",
  returnNull: "async () => null",
  returnNumber: "async () => 5",
  returnCyclic: "async () => cyclic()",
};
function inputArgs(s) {
  const [k, n] = s.split(":");
  if (k === "obj") return `, { n: ${Number(n)} }`;
  if (k === "fn") return `, { n: ${Number(n)}, f() {} }`;
  if (k === "omitted") return "";
  if (k === "toJSONNumber") return ", { toJSON() { return 5; } }";
  if (k === "cyclic") return ", cyclic()";
  throw new Error(`bad input ${s}`);
}
function toolLiteral(op) {
  const m = [`name: ${js(op.name)}`];
  if (op.title !== null) m.push(`title: ${js(op.title)}`);
  if (op.description !== null) m.push(`description: ${js(op.description)}`);
  if (op.inputSchema !== "absent") m.push(`inputSchema: ${SCHEMAS[op.inputSchema]}`);
  if (op.outputSchema !== "absent") m.push(`outputSchema: ${SCHEMAS[op.outputSchema]}`);
  if (op.annotations !== null) m.push(`annotations: ${js(op.annotations)}`);
  m.push(`execute: ${BEHAVIORS[op.behavior]}`);
  return `{ ${m.join(", ")} }`;
}

// Await `call` (an expression giving a promise) and check it settles as the model says.
function settles(call, want, onValue) {
  if (want.startsWith("err:")) {
    const name = want.slice(4);
    return name === "TypeError"
      ? [`await promise_rejects_js(t, TypeError, ${call});`]
      : [`await promise_rejects_dom(t, ${js(name)}, ${call});`];
  }
  return onValue(call);
}

// The members of each Tool a getTools() call returns, from the model's view of them
// (name|title|description|inputSchema|outputSchema|annotations, joined by ;).
function toolAsserts(v, want, namesOnly) {
  const views = want === "tools:" ? [] : want.slice(6).split(";").map((s) => s.split("|"));
  const lines = [`assert_equals(${v}.length, ${views.length}, 'getTools() returns ${views.length} tools');`];
  views.forEach(([name, title, description, input, output, annotations], i) => {
    const tv = `${v}[${i}]`;
    lines.push(`assert_equals(${tv}.name, ${js(name)});`);
    if (namesOnly) return;
    lines.push(`assert_equals(${tv}.title, ${js(title)});`);
    lines.push(`assert_equals(${tv}.description, ${js(description)});`);
    for (const [member, s] of [["inputSchema", input], ["outputSchema", output]]) {
      lines.push(s === "null"
        ? `assert_equals(${tv}.${member}, null, '${member} is null when absent');`
        : `assert_equals(JSON.stringify(${tv}.${member}), ${js(s)});`);
    }
    if (annotations === "null") {
      lines.push(`assert_equals(${tv}.annotations, null, 'annotations is null when absent');`);
    } else {
      for (const [k, b] of Object.entries(JSON.parse(annotations))) lines.push(`assert_equals(${tv}.annotations.${k}, ${b});`);
    }
  });
  return lines;
}

function testBody(ops, want) {
  const lines = [];
  let calls = 0;
  ops.forEach((op, i) => {
    const w = want[i];
    lines.push("", `// ${i + 1}. ${op.op}: the model says ${w}`);
    if (op.op === "register" || op.op === "registerAbortSync") {
      const sync = op.op === "registerAbortSync";
      const options = op.signal == null ? "" : `, { signal: controller(${op.signal}).signal }`;
      const call = `document.modelContext.registerTool(${toolLiteral(op)}${options})`;
      if (sync) {
        lines.push(`const p${i} = ${call};`, `controller(${op.signal}).abort();`);
      }
      lines.push(...settles(sync ? `p${i}` : call, w,
        (c) => [`assert_equals(await ${c}, undefined, 'registerTool() resolves');`]));
    } else if (op.op === "abort") {
      lines.push(`controller(${op.signal}).abort();`);
    } else if (op.op === "getTools") {
      const v = `tools${calls++}`;
      lines.push(`const ${v} = await document.modelContext.getTools();`, ...toolAsserts(v, w, focus && i < ops.length - 1));
    } else if (op.op === "execute") {
      const call = `document.modelContext.executeTool(tools${op.call}[${op.index}]${inputArgs(op.input)})`;
      lines.push(...settles(call, w, (c) => [`assert_equals(await ${c}, ${js(w.slice(7))});`]));
    } else {
      throw new Error(`bad op ${op.op}`);
    }
  });
  return lines;
}

function page({ title, help, source, ops, want }) {
  const body = testBody(ops, want).map((l) => (l ? `  ${l}` : l)).join("\n");
  return `<!DOCTYPE html>
<html>
<head>
<title>WebMCP: ${html(title)}</title>
${help.map((h) => `<link rel="help" href="${html(h)}">`).join("\n")}
<script src="/resources/testharness.js"></script>
<script src="/resources/testharnessreport.js"></script>
</head>
<body>
<script>
// Generated by tools/export-wpt.cjs from ${source} (webmcp-conformance). The expected
// outcomes are those of its Lean model of the spec, at spec commit ${specSha}.
promise_test(async (t) => {
  const controllers = new Map();
  const controller = (n) => {
    if (!controllers.has(n)) controllers.set(n, new AbortController());
    return controllers.get(n);
  };
  const cyclic = () => { const o = {}; o.self = o; return o; };
  t.add_cleanup(() => { for (const c of controllers.values()) c.abort(); });
${body}
}, ${js(title)});
</script>
</body>
</html>
`;
}

fs.mkdirSync(out, { recursive: true });
for (const file of inputs) {
  const data = JSON.parse(fs.readFileSync(file, "utf8"));
  const base = path.basename(file, ".json");
  const source = path.relative(root, path.resolve(file));
  data.traces.forEach((trace, n) => {
    if (only !== null && n !== only) return;
    const want = oracle(trace.ops);
    if (trace.want && JSON.stringify(trace.want) !== JSON.stringify(want)) {
      throw new Error(`${file} trace ${n}: recorded outcomes differ from the model's; refresh it first`);
    }
    const single = data.traces.length === 1;
    const title = single && data.comment?.shows ? data.comment.shows : `${base} trace ${n}`;
    const help = data.comment?.spec ?? ["https://webmachinelearning.github.io/webmcp/"];
    const name = `${base}${single ? "" : `-${n}`}.https.html`;
    fs.writeFileSync(path.join(out, name), page({ title, help, source: single ? source : `${source} (trace ${n})`, ops: trace.ops, want }));
    console.log(path.relative(process.cwd(), path.join(out, name)));
  });
}
