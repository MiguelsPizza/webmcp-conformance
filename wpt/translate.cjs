// Builds wpt/cases.json: the hand translation of WPT webmcp/ subtests into oracle traces.
// The translation is the code below; cases.json is its output, committed so the scorer needs
// neither this script nor a WPT checkout.
//
//   git clone --filter=blob:none --sparse https://github.com/web-platform-tests/wpt
//   git -C wpt sparse-checkout set webmcp && git -C wpt checkout <commit below>
//   node wpt/translate.cjs <wpt checkout> [--oracle .lake/build/bin/oracle]
//
// `execute` ops name their tool; the index into the getTools() result is filled in from the
// oracle's own getTools() outcome for the trace's prefix.
const fs = require("fs");
const path = require("path");
const { execFileSync } = require("child_process");
const argv = process.argv.slice(2);
const wptRoot = argv[0];
const oracle = argv.includes("--oracle") ? argv[argv.indexOf("--oracle") + 1] : path.join(__dirname, "../.lake/build/bin/oracle");
const outPath = path.join(__dirname, "cases.json");
if (!wptRoot) { console.error("usage: node wpt/translate.cjs <wpt checkout> [--oracle <path>]"); process.exit(2); }

const WPT_COMMIT = "e00a7b14e8e3d9c04933e29ed247baf76c60706e";
const head = execFileSync("git", ["-C", wptRoot, "rev-parse", "HEAD"]).toString().trim();
if (head !== WPT_COMMIT) console.error(`warning: checkout is at ${head}, the translation was written for ${WPT_COMMIT}`);

// Lists every testharness subtest (test/promise_test/async_test) in each file under `root`, with
// its line range and the source text of its name argument. A rough scanner, not a JS parser:
// loops and helper functions are expanded by hand in `expand` below.
function inventory(root){
function walk(d){let r=[];for(const e of fs.readdirSync(d,{withFileTypes:true})){const p=path.join(d,e.name);if(e.isDirectory())r=r.concat(walk(p));else r.push(p);}return r;}
const out=[];
for(const f of walk(root).sort()){
  const rel=path.relative(root,f);
  const src=fs.readFileSync(f,'utf8');
  const re=/(^|[^\w.])(promise_test|async_test|test)\s*\(/g; let m;
  const found=[];
  while((m=re.exec(src))){
    let i=m.index+m[0].length, depth=1, args=[], cur='', st=null;
    for(;i<src.length&&depth>0;i++){
      const c=src[i];
      if(st){cur+=c; if(c==='\\'){cur+=src[++i];continue;} if(c===st)st=null; continue;}
      if(c==='"'||c==="'"||c==='`'){st=c;cur+=c;continue;}
      if(c==='/'&&src[i+1]==='/'){while(i<src.length&&src[i]!=='\n')i++;continue;}
      if('([{'.includes(c))depth++;
      if(')]}'.includes(c))depth--;
      if(depth===0)break;
      if(c===','&&depth===1){args.push(cur);cur='';continue;}
      cur+=c;
    }
    args.push(cur);
    const line=src.slice(0,m.index+m[1].length).split('\n').length;
    const endLine=src.slice(0,i).split('\n').length;
    const name=args.length>1?args[args.length-1].trim().replace(/\s+/g,' '):'(unnamed)';
    found.push({line,endLine,kind:m[2],name});
  }
  out.push({file:rel,subtests:found});
}
return out;
}
const raw = inventory(path.join(wptRoot, "webmcp"));

// ---- op builders -------------------------------------------------------------------------
// `doc` is an index into the model's frame tree (`harnessDocs` in WebMCP/Model.lean), left out
// for the top-level document. How WPT's frames map onto it is in wpt/README.md (Method).
function reg(name, o = {}) {
  const op = {
    op: "register", name,
    title: o.title ?? null,
    description: o.description === undefined ? "d" : o.description,
    inputSchema: o.input ?? "absent", outputSchema: o.output ?? "absent",
    annotations: o.ann ?? null, behavior: o.behavior ?? "echo",
    signal: o.signal ?? null,
  };
  if (o.exposedTo) op.exposedTo = o.exposedTo;
  if (o.doc) op.doc = o.doc;
  return op;
}
const regAbortSync = (name, signal, o = {}) => ({ ...reg(name, o), op: "registerAbortSync", signal });
const abort = (signal) => ({ op: "abort", signal });
const getTools = (o = {}) => ({ op: "getTools", ...(o.fromOrigins ? { fromOrigins: o.fromOrigins } : {}), ...(o.doc ? { doc: o.doc } : {}) });
// `tool` is resolved to an index into the most recent getTools() result below.
const exec = (tool, input = "omitted", o = {}) => ({ op: "execute", call: o.call ?? "last", tool, input, ...(o.doc ? { doc: o.doc } : {}) });
// Calls started from one script before any is awaited (Op.concurrent). An `aExec` names its tool
// like `exec`, resolved against the getTools() calls before the operation; `aCancel(k)` aborts the
// execution signal of action k.
const conc = (actions, o = {}) => ({ op: "concurrent", actions, ...(o.doc ? { doc: o.doc } : {}) });
const aExec = (tool, signal = "none", input = "omitted", call = "last") => ({ act: "execute", call, tool, input, signal });
const aCancel = (target) => ({ act: "cancel", target });

// ---- expectation builders (what the WPT assertion requires, in oracle outcome form) --------
const is = (outcome) => ({ outcome });
const names = (list) => ({ names: list });
const count = (n) => ({ count: n });
const field = (tool, f, extra) => ({ tool, field: f, ...extra });
// helpers.js toolsAreEqual(): name, description, both schemas, origin, and the annotations' hints
// (which must all be undefined, so annotations null, when `annotations` is not given).
const like = (tool, expected) => ({ tool, like: expected });
// assert_false(tools.some(t => t.name === name))
const lacks = (name) => ({ lacks: name });
// exec_response.success: the promise fulfilled, whatever the string.
const resolves = () => ({ resolves: true });

const cases = [];   // translated subtests
const inScopeNames = new Set();
// `file` is relative to webmcp/imperative/, or to webmcp/ when it starts with "/".
function C(file, subtest, lines, body) {
  const rel = file.startsWith("/") ? file.slice(1) : "imperative/" + file;
  inScopeNames.add(rel + "\u0000" + subtest);
  cases.push({ file: "webmcp/" + rel, subtest, lines, scope: "in", ...body });
}

// ============================ getTools.https.html ==========================================
C("getTools.https.html", "getTools should return all tools sorted in lexicographical order", [11, 36], {
  trace: [
    reg("c", { description: "tool registered first" }),
    reg("b", { description: "tool registered second", signal: 0 }),
    reg("a", { description: "tool registered last" }),
    getTools(), abort(0), getTools()],
  checks: [
    { at: 0, line: 19, assert: "await registerTool(tool_c) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 20, assert: "await registerTool(tool_b, {signal}) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 21, assert: "await registerTool(tool_a) fulfils", want: is("ok"), setup: true },
    { at: 3, line: 24, assert: "tools.length == 3, names a, b, c", want: names(["a", "b", "c"]) },
    { at: 5, line: 33, assert: "after abort: tools.length == 2, names a, c", want: names(["a", "c"]) }],
});

// ============================ register_tool_name_validation.https.html =====================
const validNames = ["a", "A", "0", "valid-name", "valid_name", "valid.name", "valid-name.with_extras-123", "a".repeat(128)];
const invalidNames = ["", "a".repeat(129), "name with space", "name@special", "name#special", "name$special",
  "name%", "name^", "name&", "name*", "name(", "name)", "name+", "name=", "name[", "name]", "name{", "name}",
  "name|", "name\\", "name:", "name;", "name\"", "name'", "name<", "name>", "name?", "name/", "name`", "name~"];
const validRegs = validNames.map((n) => reg(n, { description: "valid name test", behavior: "returnText" }));
C("register_tool_name_validation.https.html", "Valid tool names are accepted.", [11, 31], {
  trace: validRegs,
  checks: validNames.map((n, i) => ({ at: i, line: 25, assert: `registerTool name ${JSON.stringify(n.length > 20 ? n.slice(0, 3) + "...(" + n.length + ")" : n)} fulfils`, want: is("ok") })),
  notes: "execute is `async () => 'empty'`; modelled as returnText (never executed).",
});
C("register_tool_name_validation.https.html", "Invalid tool names throw InvalidStateError.", [33, 79], {
  setup: validRegs,
  setupNote: "the tools the previous subtest registered (never unregistered)",
  trace: invalidNames.map((n) => reg(n, { description: "invalid name test", behavior: "returnText" })),
  checks: invalidNames.map((n, i) => ({ at: i, line: 69, assert: `registerTool name ${JSON.stringify(n.length > 20 ? n.slice(0, 3) + "...(" + n.length + ")" : n)} rejects InvalidStateError`, want: is("err:InvalidStateError") })),
});

// ============================ register_tool_with_schema.https.html =========================
C("register_tool_with_schema.https.html", "register and unregister script tool", [11, 34], {
  trace: [reg("echo", { description: "echo input", input: "object", ann: { readOnlyHint: true }, signal: 0 }), abort(0)],
  checks: [{ at: 0, line: 32, assert: "await registerTool(tool, {signal}) fulfils", want: is("ok"),
    proxy: "inputSchema {type:'object', properties:{text:...}, required:[...]} -> model `object`; annotations {readOnlyHint: 'true'} (a string, which Web IDL converts to boolean true) -> {readOnlyHint: true}" }],
});
C("register_tool_with_schema.https.html", "registerTool succeeds when inputSchema.toJSON() returns 'undefined'", [36, 47], {
  trace: [reg("empty", { description: "empty", input: "viaToJSON" })],
  checks: [{ at: 0, line: 37, assert: "await registerTool(...) fulfils", want: is("ok"),
    proxy: "inputSchema whose toJSON() returns the string 'undefined' -> model `viaToJSON` (toJSON() returns {type:'string'}); both make 'serialize a tool schema' call toJSON() and succeed. The model has no schema whose toJSON() returns a primitive; see the README on what getTools() should then expose." }],
});
C("register_tool_with_schema.https.html", "register and unregister script tool with outputSchema", [49, 69], {
  setup: [reg("empty", { description: "empty", input: "viaToJSON" })],
  setupNote: "'empty' from the previous subtest",
  trace: [reg("output_tool", { description: "tool with output schema", output: "object", signal: 1 }), abort(1)],
  checks: [{ at: 0, line: 67, assert: "await registerTool(tool, {signal}) fulfils", want: is("ok"),
    proxy: "outputSchema {type:'object', properties:..., required:[...]} -> model `object`" }],
});
C("register_tool_with_schema.https.html", "registerTool succeeds when outputSchema.toJSON() returns 'undefined'", [71, 82], {
  setup: [reg("empty", { description: "empty", input: "viaToJSON" })],
  setupNote: "'empty' from the second subtest",
  trace: [reg("empty_output_undefined_string", { description: "empty", output: "viaToJSON" })],
  checks: [{ at: 0, line: 72, assert: "await registerTool(...) fulfils", want: is("ok"),
    proxy: "outputSchema whose toJSON() returns the string 'undefined' -> model `viaToJSON`" }],
});

// ============================ register_tool_no_schema.https.html ===========================
C("register_tool_no_schema.https.html", "register tool with only required params", [11, 21], {
  trace: [reg("empty", { description: "echo empty", signal: 0 }), abort(0)],
  checks: [{ at: 0, line: 19, assert: "await registerTool(tool, {signal}) fulfils", want: is("ok") }],
});

// ============================ register_tool_with_empty_annotation.https.html ===============
C("register_tool_with_empty_annotation.https.html", "register tool with empty annotations", [11, 24], {
  trace: [reg("echo", { description: "echo input", ann: {}, signal: 0 }), abort(0)],
  checks: [{ at: 0, line: 22, assert: "await registerTool(tool, {signal}) fulfils", want: is("ok") }],
});

// ============================ duplicate_tool_registration.https.html =======================
C("duplicate_tool_registration.https.html", "duplicate tool registration is invalid.", [11, 30], {
  trace: [reg("empty", { description: "echo empty", behavior: "returnText" }), reg("empty", { description: "echo empty", behavior: "returnText" })],
  checks: [
    { at: 0, line: 16, assert: "await registerTool(empty) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 22, assert: "second registerTool(empty) rejects InvalidStateError", want: is("err:InvalidStateError") }],
});

// ============================ register_tool_signal.https.html ==============================
C("register_tool_signal.https.html", "register tool promise rejects with AbortError when signal gets aborted", [17, 22], {
  trace: [regAbortSync("empty", 0, { description: "empty" })],
  checks: [{ at: 0, line: 21, assert: "registerTool(tool, {signal}); controller.abort(); promise rejects AbortError", want: is("err:AbortError") }],
});
C("register_tool_signal.https.html", "register tool promise rejects with error when signal gets aborted", [24, 30], {
  trace: [regAbortSync("empty", 1, { description: "empty" })],
  checks: [{ at: 0, line: 29, assert: "registerTool(tool, {signal}); controller.abort(error); promise rejects with exactly error", want: is("err:AbortError"),
    proxy: "controller.abort(new Error('abort error')) -> an abort with the default reason (an AbortError DOMException); either way the abort steps reject the promise with the signal's abort reason (index.bs L893-L898). This is the previous subtest's trace: the custom reason is the only difference, and the model doesn't have it" }],
});
C("register_tool_signal.https.html", "register tool promise rejects when signal is already aborted", [32, 36], {
  trace: [abort(2), reg("empty", { description: "empty", signal: 2 })],
  checks: [{ at: 1, line: 35, assert: "registerTool(tool, {signal: AbortSignal.abort('aborted')}) rejects with exactly 'aborted'", want: is("err:AbortError"),
    proxy: "AbortSignal.abort('aborted') -> a signal the trace aborts first, with the default reason; registerTool() rejects with the signal's abort reason (index.bs L866-L868)" }],
});
C("register_tool_signal.https.html", "aborting signal unregister tool", [38, 51], {
  setupNote: "the earlier subtests leave no tool registered (each registration is aborted)",
  trace: [getTools(), reg("empty", { description: "empty", signal: 3 }), getTools(), abort(3), getTools()],
  checks: [
    { at: 0, line: 40, assert: "tools.length == 0", want: count(0) },
    { at: 1, line: 43, assert: "await registerTool(tool, {signal}) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 46, assert: "tools.length == 1", want: count(1) },
    { at: 4, line: 50, assert: "after abort: tools.length == 0", want: count(0) }],
});

// ============================ register_tool_invalid_json_schema.https.html =================
for (const [which, member] of [["input", "inputSchema"], ["output", "outputSchema"]]) {
  const base = which === "input" ? { line: 13, calls: [27, 32, 41], aborted: [46, 71], assertAborted: 52 } : { line: 75, calls: [89, 94, 103], aborted: [108, 133], assertAborted: 114 };
  const nm = which === "input" ? "empty" : "empty_output";
  const k = which === "input" ? "input" : "output";
  C("register_tool_invalid_json_schema.https.html", `registerTool rejects when ${member}.toJSON() returns undefined`, [base.calls[0], base.calls[0] + 3], {
    trace: [reg(nm, { description: "empty", [k]: "unserializable" })],
    checks: [{ at: 0, line: base.line, assert: "registerTool rejects TypeError", want: is("err:TypeError"),
      proxy: `${member} {toJSON: () => undefined} -> model \`unserializable\` (a cycle). Both make 'serializing a JavaScript value to a JSON string' throw a TypeError (spec.bs 'serialize a tool schema' note).` }],
  });
  C("register_tool_invalid_json_schema.https.html", `registerTool rejects when ${member} contains a circular reference`, [base.calls[1], base.calls[1] + 7], {
    trace: [reg(nm, { description: "empty", [k]: "unserializable" })],
    checks: [{ at: 0, line: base.line, assert: "registerTool rejects TypeError", want: is("err:TypeError") }],
  });
  C("register_tool_invalid_json_schema.https.html", `registerTool rejects when ${member} contains non-serializable types (BigInt)`, [base.calls[2], base.calls[2] + 3], {
    trace: [reg(nm, { description: "empty", [k]: "nonObject" })],
    checks: [{ at: 0, line: base.line, assert: "registerTool rejects TypeError", want: is("err:TypeError"),
      proxy: `${member}: BigInt(42) -> model \`nonObject\` (the string "x"). Both fail Web IDL conversion to \`object\` with a TypeError before any method step.` }],
  });
  C("register_tool_invalid_json_schema.https.html", `registerTool rejects on invalid ${which === "input" ? "" : "output "}schema even if an aborted signal was provided`, base.aborted, {
    trace: [abort(9), reg(which === "input" ? "aborted_invalid_schema" : "aborted_invalid_output_schema", { description: "empty", [k]: "unserializable", signal: 9 })],
    checks: [{ at: 1, line: base.assertAborted, assert: "registerTool with circular schema and AbortSignal.abort('aborted') rejects TypeError (schema checked before signal)", want: is("err:TypeError"),
      proxy: "AbortSignal.abort('aborted') -> a signal the trace aborts first (default reason); the reason is never observed because the TypeError wins" }],
  });
}

// ============================ getTools-imperative-annotations.https.html ===================
const annCases = [
  ["Test that getTools() returns explicit annotations for an imperative tool", [9, 37], "annotated_tool", "A tool with explicit annotations",
    { readOnlyHint: true, untrustedContentHint: true, consequentialHint: false, debugging: true },
    { readOnlyHint: true, untrustedContentHint: true, consequentialHint: false, debugging: true }, 24, 35],
  ["Test that getTools() populates default values for omitted annotation properties", [39, 64], "partial_annotated_tool", "A tool with only readOnlyHint supplied",
    { readOnlyHint: true }, { readOnlyHint: true, untrustedContentHint: false, consequentialHint: false, debugging: false }, 51, 62],
  ["Test that getTools() returns default values when annotations object is empty", [66, 89], "empty_annotated_tool", "A tool with empty annotations object",
    {}, { readOnlyHint: false, untrustedContentHint: false, consequentialHint: false, debugging: false }, 76, 87],
  ["Test that getTools() returns null annotations when omitted at registration", [91, 105], "unannotated_tool", "A tool without annotations property",
    null, null, 100, 104],
];
annCases.forEach(([name, lines, tname, desc, ann, want, regLine, assertLine], i) => {
  C("getTools-imperative-annotations.https.html", name, lines, {
    setupNote: i ? "earlier subtests' tools are unregistered by their cleanup" : undefined,
    trace: [reg(tname, { description: desc, ann, signal: i }), getTools(), abort(i)],
    checks: [
      { at: 0, line: regLine, assert: "await registerTool(tool, {signal}) fulfils", want: is("ok"), setup: true },
      want === null
        ? { at: 1, line: assertLine, assert: "registeredTool.annotations === null", want: field(tname, "annotations", { isNull: true }) }
        : { at: 1, line: assertLine, assert: `assert_object_equals(annotations, ${JSON.stringify(want)})`, want: field(tname, "annotations", { json: want }) }],
  });
});

// ============================ getTools-imperative-schema.https.html ========================
C("getTools-imperative-schema.https.html", "Test that getTools() returns the correct inputSchema for an imperative tool", [9, 63], {
  trace: [reg("search_tool", { description: "Search the web", input: "object" }), getTools()],
  checks: [
    { at: 0, line: 34, assert: "await registerTool(tool) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 37, assert: "tools.length == 1", want: count(1) },
    { at: 1, line: 40, assert: "name == 'search_tool'", want: field("search_tool", "name", { equals: "search_tool" }) },
    { at: 1, line: 41, assert: "description == 'Search the web'", want: field("search_tool", "description", { equals: "Search the web" }) },
    { at: 1, line: 43, assert: "inputSchema is non-null", want: field("search_tool", "inputSchema", { notNull: true }) },
    { at: 1, line: 44, assert: "inputSchema.type == 'object'", want: field("search_tool", "inputSchema", { path: "type", equals: "object" }),
      proxy: "the WPT schema {type:'object', properties:{query, limit, safe_search}, required:['query']} -> model `object` ({type:'object'})" },
    { at: 1, line: 62, assert: "outputSchema === null", want: field("search_tool", "outputSchema", { isNull: true }) }],
  notExpressible: [{ line: "47-60", assert: "inputSchema.properties.* and .required round-trip",
    why: "the model's schemas are {type:'object'} and {type:'string'} only; nested members are a property of JSON round-tripping, not of any spec step the model encodes" }],
});
C("getTools-imperative-schema.https.html", "Test that getTools() returns the correct outputSchema for an imperative tool", [65, 96], {
  setup: [reg("search_tool", { description: "Search the web", input: "object" })],
  setupNote: "'search_tool' from the previous subtest (no signal, never unregistered)",
  trace: [reg("output_schema_tool", { description: "Tool with output schema", output: "object", signal: 0 }), getTools(), abort(0)],
  checks: [
    { at: 0, line: 83, assert: "await registerTool(tool, {signal}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 88, assert: "tool is found", want: field("output_schema_tool", "name", { equals: "output_schema_tool" }), setup: true },
    { at: 1, line: 89, assert: "inputSchema === null", want: field("output_schema_tool", "inputSchema", { isNull: true }) },
    { at: 1, line: 90, assert: "outputSchema is non-null", want: field("output_schema_tool", "outputSchema", { notNull: true }) },
    { at: 1, line: 91, assert: "outputSchema.type == 'object'", want: field("output_schema_tool", "outputSchema", { path: "type", equals: "object" }),
      proxy: "the WPT outputSchema (with properties and required) -> model `object`" }],
  notExpressible: [{ line: "92-95", assert: "outputSchema.properties.result.* and .required", why: "as in the previous subtest" }],
});

// ============================ register-tool-title.https.html ===============================
C("register-tool-title.https.html", "Tool title is preserved when provided", [14, 26], {
  trace: [reg("with-title", { title: "My Custom Title", description: "tool with title", behavior: "returnText" }), getTools()],
  checks: [
    { at: 0, line: 15, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 25, assert: "tool.title == 'My Custom Title'", want: field("with-title", "title", { equals: "My Custom Title" }) }],
});
C("register-tool-title.https.html", "Missing tool title in registration is exposed as empty string", [28, 41], {
  setup: [reg("with-title", { title: "My Custom Title", description: "tool with title", behavior: "returnText" })],
  setupNote: "'with-title' from the previous subtest",
  trace: [reg("without-title", { description: "tool without title", behavior: "returnText" }), getTools()],
  checks: [
    { at: 0, line: 29, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 40, assert: "tool.title == ''", want: field("without-title", "title", { equals: "" }) }],
});
C("register-tool-title.https.html", "Tool title with unpaired surrogate is fixed up by USVString", [43, 57], {
  trace: [], checks: [],
  notExpressible: [{ line: 56, assert: "title '\\uD800' comes back as '\\uFFFD'",
    why: "USVString conversion is Web IDL, not a spec step the model encodes, and the oracle's strings (Lean String over JSON) cannot hold a lone surrogate" }],
});

// ============================ object-arguments.https.html ==================================
C("object-arguments.https.html", "tool execution requires a JSON Object input argument; and Arrays are Objects", [7, 75], {
  trace: [reg("test-tool", { description: "Tool for testing various JSON primitive inputs", behavior: "returnText" }), getTools(),
    exec("test-tool", "cyclic"), exec("test-tool", "omitted"), exec("test-tool", "omitted"), exec("test-tool", "omitted")],
  checks: [
    { at: 0, line: 18, assert: "await registerTool(tool) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 51, assert: "executeTool(tool, {toJSON: () => undefined}) rejects TypeError", want: is("err:TypeError"),
      proxy: "input {toJSON: () => undefined} -> model `cyclic`; both make 'serializing a JavaScript value to a JSON string' throw TypeError (executeTool() step 8)" },
    { at: 3, line: 58, assert: "executeTool(tool) resolves with \"Success\"", want: is("result:hi"),
      proxy: "the tool returns the string 'Success' -> model `returnText` (returns 'hi'); the WPT assertion is that the result is the returned string itself, so 'hi'" },
    { at: 4, line: 66, assert: "executeTool(tool, undefined) resolves with \"Success\"", want: is("result:hi"),
      proxy: "as above; Web IDL treats an explicit undefined for an optional argument as missing, so the input is `omitted`" },
    { at: 5, line: 73, assert: "executeTool(tool, undefined, {}) resolves with \"Success\"", want: is("result:hi"),
      proxy: "as above; options {} has no signal, which the model never uses" }],
  extra: {
    note: "The tool also records the argument it received. The model's `keys` behaviour reports Object.keys of it, so a second trace checks the assert_object_equals(executeReceivedArgs, {}) lines.",
    trace: [reg("test-tool", { description: "Tool for testing various JSON primitive inputs", behavior: "keys" }), getTools(),
      exec("test-tool", "omitted"), exec("test-tool", "omitted"), exec("test-tool", "omitted")],
    checks: [
      { at: 2, line: 59, assert: "executeReceivedArgs equals {} after executeTool(tool)", want: is("result:[]"), proxy: "Object.keys(received) == [] stands for assert_object_equals(received, {})" },
      { at: 3, line: 67, assert: "executeReceivedArgs equals {} after executeTool(tool, undefined)", want: is("result:[]"), proxy: "as above" },
      { at: 4, line: 74, assert: "executeReceivedArgs equals {} after executeTool(tool, undefined, {})", want: is("result:[]"), proxy: "as above" }],
  },
  notExpressible: [
    { line: "23-25", assert: "executeTool(tool, [1,2,3]) resolves 'Success' and the tool receives [1,2,3]", why: "the model has no array input (an Array is an Object, so the spec runs the tool; the result would again be a #361 case)" },
    { line: 29, assert: "executeTool(tool, 'hello') rejects TypeError", why: "the model has no primitive inputs; Web IDL conversion of a string to `object` throws TypeError (spec IDL: `optional object inputObject`)" },
    { line: 34, assert: "executeTool(tool, 123) rejects TypeError", why: "as above" },
    { line: 39, assert: "executeTool(tool, true) rejects TypeError", why: "as above" },
    { line: 44, assert: "executeTool(tool, null) rejects TypeError", why: "as above (`object` is not nullable)" }],
});

// ============================ executeTool-invalid-dictionary.https.html ====================
C("executeTool-invalid-dictionary.https.html", "executeTool() rejects with TypeError when passed an object that is not a Tool", [10, 37], {
  trace: [reg("legit_tool", { description: "Legitimate tool description", behavior: "returnText" }), getTools()],
  checks: [
    { at: 0, line: 11, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 19, assert: "legit_tool is discovered", want: field("legit_tool", "name", { equals: "legit_tool" }), setup: true }],
  notExpressible: [{ line: "31-36", assert: "executeTool(lookalike plain object) rejects TypeError",
    why: "the model only executes Tool objects that getTools() returned; Web IDL interface conversion of a non-Tool is not modelled" }],
});
C("executeTool-invalid-dictionary.https.html", "executeTool() rejects with TypeError for invalid JSON arguments", [39, 75], {
  setup: [reg("legit_tool", { description: "Legitimate tool description", behavior: "returnText" })],
  setupNote: "'legit_tool' from the previous subtest",
  trace: [reg("json-test-tool", { description: "Tool for JSON tests", behavior: "returnText" }), getTools(),
    exec("json-test-tool", "cyclic"), exec("json-test-tool", "cyclic")],
  checks: [
    { at: 0, line: 40, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 48, assert: "json-test-tool is discovered", want: field("json-test-tool", "name", { equals: "json-test-tool" }), setup: true },
    { at: 2, line: 52, assert: "executeTool(tool, circular) rejects TypeError", want: is("err:TypeError") },
    { at: 3, line: 62, assert: "executeTool(tool, {toJSON: () => undefined}) rejects TypeError", want: is("err:TypeError"),
      proxy: "input {toJSON: () => undefined} -> model `cyclic` (same serialization step)" }],
  notExpressible: [{ line: 69, assert: "executeTool(tool, BigInt(42)) rejects TypeError", why: "no primitive inputs in the model; this is Web IDL conversion to `object`" }],
});

// ============================ tool-re-registration-race.https.html =========================
C("tool-re-registration-race.https.html", "executeTool() rejects for a Tool that was unregistered and whose name was subsequently reused by a different tool", [15, 69], {
  trace: [reg("race_tool", { description: "the original tool", behavior: "echo", signal: 0 }), getTools(), abort(0),
    reg("race_tool", { description: "a different tool that reused the name", behavior: "echo" }),
    { ...exec("race_tool", "omitted"), call: 0 }, getTools(), exec("race_tool", "omitted")],
  checks: [
    { at: 0, line: 22, assert: "await registerTool(original, {signal}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 32, assert: "stale_tool.description == 'the original tool'", want: field("race_tool", "description", { equals: "the original tool" }) },
    { at: 3, line: 37, assert: "await registerTool(replacement) fulfils", want: is("ok"), setup: true },
    { at: 4, line: 51, assert: "executeTool(stale_tool, {}) rejects NotFoundError", want: is("err:NotFoundError") },
    { at: 5, line: 63, assert: "fresh_tool.description == 'a different tool that reused the name'", want: field("race_tool", "description", { equals: "a different tool that reused the name" }) },
    { at: 6, line: 64, assert: "executeTool(fresh_tool, {}) resolves with the JSON of the returned object", want: is("result:{}"),
      proxy: "the tool returns {which:'second'} and WPT expects '{\"which\":\"second\"}'; the model's object-returning behaviour is `echo`, which returns the received {} , so the same assertion reads '{}'. {} passed explicitly serializes like the omitted default." }],
  notExpressible: [{ line: "48-49, 55-58, 66-67", assert: "stale_tool still describes the old tool after re-registration; first_executed/second_executed flags",
    why: "Tool objects are immutable snapshots in the model, and it does not record which callback ran beyond the outcome; covered implicitly by the NotFoundError and the fresh result" }],
});

// ============================ executeTool-error-window-onerror.https.html ==================
const onerror = [
  ["Failed tool execution does not trigger window.onerror", [11, 40], "throwing_tool", "A tool that throws an error", "reject", 22, 35, 39, null],
  ["Tool execution returning circular object rejects and does not trigger window.onerror", [42, 73], "circular_tool", "A tool that returns a circular object", "returnCyclic", 53, 68, 72, null],
  ["Tool execution returning a Symbol rejects and does not trigger window.onerror", [101, 126], "symbol_tool", "A tool that returns a Symbol", "returnUndefined", 111, 121, 125,
    "the tool returns Symbol('result') -> model `returnUndefined`: JSON.stringify yields undefined for both, so 'serializing a JavaScript value to a JSON string' throws TypeError and the spec reports 'unserializable result'"],
  ["Tool execution returning an object with a BigInt property rejects and does not trigger window.onerror", [101, 126], "bigint_property_tool", "A tool that returns an object with a BigInt property", "returnCyclic", 111, 121, 125,
    "the tool returns {value: 1n} -> model `returnCyclic`: JSON.stringify throws for both"],
  ["Tool execution returning an object whose toJSON() throws rejects and does not trigger window.onerror", [101, 126], "throwing_tojson_tool", "A tool that returns an object whose toJSON() throws", "returnCyclic", 111, 121, 125,
    "the tool returns an object whose toJSON() throws -> model `returnCyclic`: JSON.stringify throws for both"],
  ["Tool execution returning an object with a throwing getter rejects and does not trigger window.onerror", [101, 126], "throwing_getter_tool", "A tool that returns an object with a throwing getter", "returnCyclic", 111, 121, 125,
    "the tool returns an object with a throwing getter -> model `returnCyclic`: JSON.stringify throws for both"],
];
const onerrorRegs = [];
onerror.forEach(([name, lines, tname, desc, beh, regLine, rejLine, errLine, proxy]) => {
  C("executeTool-error-window-onerror.https.html", name, lines, {
    setup: [...onerrorRegs],
    setupNote: onerrorRegs.length ? "tools registered by earlier subtests (never unregistered)" : undefined,
    trace: [reg(tname, { description: desc, behavior: beh }), getTools(), exec(tname, "omitted")],
    checks: [
      { at: 0, line: regLine, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
      { at: 2, line: rejLine, assert: "executeTool(tool) rejects OperationError", want: is("err:OperationError"),
        ...(proxy ? { proxy } : beh === "reject" ? { proxy: "an async function that throws returns a rejected promise -> model `reject`" } : {}) }],
    notExpressible: [{ line: errLine, assert: "no window error event fires", why: "error events / console reporting are not modelled" }],
  });
  onerrorRegs.push(reg(tname, { description: desc, behavior: beh }));
});

// ---- frames and origins --------------------------------------------------------------------
// WPT's documents map onto the model's frame tree (harnessDocs): the test page is document 0
// (origin 0); a same-origin <iframe> is document 1; an HTTPS_REMOTE_ORIGIN <iframe> with
// allow="tools ..." is document 3 (origin 1), and without it document 4; an
// HTTPS_OTHER_NOTSAMESITE_ORIGIN frame is document 2 (origin 2), and that origin is origin 3 when
// the test has no document of it. Signals are numbered by document: 0-2 for document 0, 3-5 for
// 1, 6-8 for 2, 9-11 for 3. Each WPT subtest removes its iframes in cleanup, which takes their
// tools with them, so a later subtest's setup only replays tools of the test page itself.
const O = (n) => "origin:" + n;
const iframeResult = "the iframe's tool returns 'hello from iframe' (resources/iframe-register-tool.html) -> model `returnText` ('hi')";
const toolchange = (line, what) => ({ line, assert: what, why: "toolchange events are not modelled" });
const stringResult = (s) => `the tool returns the string '${s}' -> model \`returnText\` ('hi'); the WPT assertion is that the result is the returned string itself, so 'hi'`;
const customReason = (r) => `the execution signal is aborted with the reason ${r} -> the model's signal, which aborts with the default reason (an AbortError DOMException); either way executeTool()'s abort steps "Reject promise with signal's abort reason" (index.bs L1146-L1148 at 14b6d53)`;
const afterStart = "WPT aborts after awaiting the callback's start; the model's `cancel` runs in the same script, before the queued tool execute steps. The abort steps reject the promise whenever they run, and cancelling doesn't stop a callback that has started, so the outcome is the same";
const neverSettles = "execute returns a promise that never settles -> model `returnText`; the promise is rejected by the abort before the callback's outcome could matter";

// ============================ exposedTo-cross-origin-child.https.html ========================
C("exposedTo-cross-origin-child.https.html", "Parent exposes tool to cross-origin child", [28, 82], {
  trace: [reg("parent_tool_exposed", { description: "Parent tool exposed to child", input: "object", behavior: "returnText", signal: 0, exposedTo: [O(1)] }),
    getTools({ doc: 3, fromOrigins: [O(0)] }),
    getTools({ doc: 3, fromOrigins: [O(0)] }), exec("parent_tool_exposed", "omitted", { doc: 3 }),
    abort(0), getTools({ doc: 3, fromOrigins: [O(0)] })],
  checks: [
    { at: 0, line: 30, assert: "await registerTool(tool, {exposedTo: [REMOTE], signal}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 44, assert: "the iframe's getTools({fromOrigins: [self.origin]}) returns the parent's tool, origin self.origin (toolsAreEqual)", want: like("parent_tool_exposed", { name: "parent_tool_exposed", description: "Parent tool exposed to child", inputSchema: { type: "object" }, outputSchema: null, origin: 0 }),
      proxy: "inputSchema {type:'object', properties:{query:...}} -> model `object` ({type:'object'})" },
    { at: 3, line: 61, assert: "the iframe's executeTool(tool) of the parent's tool fulfils", want: resolves() },
    { at: 3, line: 62, assert: "the iframe gets 'hello'", want: is("result:hi"), proxy: stringResult("hello") },
    { at: 5, line: 81, assert: "after controller.abort(), the iframe's getTools() returns []", want: count(0) }],
  notes: "The iframe's 'execute' message runs getTools(options) and then executeTool(tool, {}); {} serializes like the omitted input.",
  notExpressible: [toolchange(76, "the cross-origin iframe receives toolchange on unregistration")],
});
C("exposedTo-cross-origin-child.https.html", "Cross-origin child exposes tool to parent", [84, 127], {
  trace: [reg("iframe_tool_exposed", { doc: 3, description: "Iframe tool exposed to parent", input: "object", behavior: "returnText", signal: 9, exposedTo: [O(0)] }),
    getTools({ fromOrigins: [O(1)] }), exec("iframe_tool_exposed"), abort(9), getTools({ fromOrigins: [O(1)] })],
  checks: [
    { at: 0, line: 80, assert: "the iframe's await registerTool(tool, {exposedTo: [parent], signal}) fulfils (resources/iframe-register-tool.html)", want: is("ok"), setup: true },
    { at: 1, line: 105, assert: "getTools({fromOrigins: [REMOTE]}) includes the iframe's tool, origin REMOTE (toolsAreEqual)", want: like("iframe_tool_exposed", { name: "iframe_tool_exposed", description: "Iframe tool exposed to parent", inputSchema: { type: "object" }, outputSchema: null, origin: 1 }),
      proxy: "inputSchema {type:'object', properties:{query:...}} -> model `object`" },
    { at: 2, line: 115, assert: "executeTool(tool) resolves with 'hello from iframe'", want: is("result:hi"), proxy: iframeResult },
    { at: 4, line: 126, assert: "after the iframe unregisters, getTools({fromOrigins: [REMOTE]}) returns []", want: count(0) }],
});
C("exposedTo-cross-origin-child.https.html", "Parent exposes tool to origin that is neither its own nor its iframe's", [129, 159], {
  trace: [reg("parent_tool", { description: "Parent tool exposed", behavior: "returnText", signal: 0, exposedTo: [O(3)] }),
    getTools({ doc: 3, fromOrigins: [O(0)] }), abort(0)],
  checks: [
    { at: 0, line: 132, assert: "await registerTool(tool, {exposedTo: [OTHER], signal}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 144, assert: "the iframe's getTools({fromOrigins: [self.origin]}) returns []", want: count(0) }],
  notExpressible: [toolchange(158, "the iframe does not receive toolchange")],
});
C("exposedTo-cross-origin-child.https.html", "Iframe exposes tool to origin that is neither its own nor its parent's", [161, 194], {
  trace: [reg("iframe_tool", { doc: 3, description: "Iframe tool", behavior: "returnText", signal: 9, exposedTo: [O(3)] }),
    getTools({ fromOrigins: [O(1)] }), getTools({ fromOrigins: [O(1)] })],
  checks: [
    { at: 0, line: 80, assert: "the iframe's await registerTool(tool, {exposedTo: [OTHER]}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 185, assert: "getTools({fromOrigins: [REMOTE]}) returns []", want: count(0) },
    { at: 2, line: 193, assert: "after the 'unregister' message, getTools({fromOrigins: [REMOTE]}) still returns []", want: count(0) }],
  notes: "L187 asks the iframe to unregister 'iframe_tool_to_c', a name it never registered, so the iframe aborts nothing and iframe_tool stays registered; the trace has no abort. The assertion holds either way.",
  notExpressible: [toolchange(166, "the parent receives no toolchange event")],
});

// ============================ exposedTo-defaults-cross-origin.https.html =====================
for (const [sub, lines, nm, desc, exp] of [
  ["Parent tool with no exposedTo array is not visible to cross-origin iframe", [28, 56], "parent_tool_default", "Parent tool with default exposure", undefined],
  ["Parent tool with empty exposedTo array is not visible to cross-origin iframe", [58, 85], "parent_tool_empty", "Parent tool with empty exposedTo", []]]) {
  C("exposedTo-defaults-cross-origin.https.html", sub, lines, {
    trace: [reg(nm, { description: desc, behavior: "returnText", signal: 0, exposedTo: exp }), getTools({ doc: 3 }), abort(0)],
    checks: [
      { at: 0, line: lines[0] + 2, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
      { at: 1, line: lines[0] + 13 - (exp ? 1 : 0), assert: "the cross-origin iframe's getTools() returns []", want: count(0) }],
    notExpressible: [toolchange(lines[1] - 1, "the cross-origin iframe receives no toolchange on unregistration")],
  });
}
for (const [sub, lines, nm, desc, exp, l1, l2] of [
  ["Cross-origin iframe tool with default exposure is not visible to parent", [87, 117], "iframe_tool_default", "Iframe tool with default exposure", undefined, 110, 116],
  ["Cross-origin iframe tool with empty exposedTo array is not visible to parent", [119, 150], "iframe_tool_empty", "Iframe tool with empty exposedTo", [], 143, 149]]) {
  C("exposedTo-defaults-cross-origin.https.html", sub, lines, {
    trace: [reg(nm, { doc: 3, description: desc, behavior: "returnText", signal: 9, exposedTo: exp }), getTools(), abort(9), getTools()],
    checks: [
      { at: 0, line: 80, assert: "the iframe's await registerTool(...) fulfils (resources/iframe-register-tool.html)", want: is("ok"), setup: true },
      { at: 1, line: l1, assert: "getTools() returns []", want: count(0) },
      { at: 3, line: l2, assert: "after the iframe unregisters, getTools() has no " + nm, want: lacks(nm) }],
    notExpressible: [toolchange(lines[0] + 5, "the parent receives no toolchange event")],
  });
}

// ============================ exposedTo-defaults-same-origin.https.html ======================
{
  const ann = { readOnlyHint: true, untrustedContentHint: false, consequentialHint: false, debugging: false };
  for (const [sub, lines, nm, desc, exp, a, L] of [
    ["Parent tool with missing `exposedTo` array is visible to same-origin iframe", [23, 73], "parent_tool_default", "Parent tool with default exposure", undefined, ann, { reg: 25, seen: 40, eq: 41, ok: 53, res: 54, tc: 68, gone: 72 }],
    ["Parent tool with empty `exposedTo` array is visible to same-origin iframe", [75, 122], "parent_tool_empty", "Parent tool with empty exposedTo", [], undefined, { reg: 77, seen: 90, eq: 91, ok: 102, res: 103, tc: 117, gone: 121 }]]) {
    C("exposedTo-defaults-same-origin.https.html", sub, lines, {
      trace: [reg(nm, { description: desc, input: "object", ann: a, behavior: "returnText", signal: 0, exposedTo: exp }),
        getTools({ doc: 1 }), getTools({ doc: 1 }), exec(nm, "omitted", { doc: 1 }), abort(0), getTools({ doc: 1 })],
      checks: [
        { at: 0, line: L.reg, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
        { at: 1, line: L.seen, assert: "the same-origin iframe's getTools() returns the parent's tool", want: field(nm, "name", { equals: nm }) },
        { at: 1, line: L.eq, assert: "toolsAreEqual(tool, {...}), origin self.origin", want: like(nm, { name: nm, description: desc, inputSchema: { type: "object" }, outputSchema: null, ...(a ? { annotations: a } : {}), origin: 0 }),
          proxy: "inputSchema {type:'object', properties:{query:...}} -> model `object`" },
        { at: 3, line: L.ok, assert: "the iframe's executeTool(tool) fulfils", want: resolves() },
        { at: 3, line: L.res, assert: "the iframe gets 'hello'", want: is("result:hi"), proxy: stringResult("hello") },
        { at: 5, line: L.gone, assert: "after controller.abort(), the iframe's getTools() returns []", want: count(0) }],
      notes: "The iframe's 'execute' message runs getTools() and then executeTool(tool, {}); {} serializes like the omitted input.",
      notExpressible: [toolchange(L.tc, "the same-origin iframe receives toolchange on unregistration")],
    });
  }
  for (const [sub, lines, nm, desc, exp, L] of [
    ["Same-origin iframe tool with default exposure is visible to parent", [124, 162], "iframe_tool_default", "Iframe tool with default exposure", undefined, { eq: 141, res: 151, gone: 161 }],
    ["Same-origin iframe tool with empty exposedTo array is visible to parent", [164, 203], "iframe_tool_empty", "Iframe tool with empty exposedTo", [], { eq: 182, res: 192, gone: 202 }]]) {
    C("exposedTo-defaults-same-origin.https.html", sub, lines, {
      trace: [reg(nm, { doc: 1, description: desc, behavior: "returnText", signal: 3, exposedTo: exp }), getTools(), exec(nm), abort(3), getTools()],
      checks: [
        { at: 0, line: 80, assert: "the iframe's await registerTool(...) fulfils (resources/iframe-register-tool.html)", want: is("ok"), setup: true },
        { at: 1, line: L.eq, assert: "[tool] = getTools() is the iframe's tool, origin iframe.contentWindow.origin (toolsAreEqual)", want: like(nm, { name: nm, description: desc, inputSchema: null, outputSchema: null, origin: 0 }) },
        { at: 2, line: L.res, assert: "executeTool(tool) resolves with 'hello from iframe'", want: is("result:hi"), proxy: iframeResult },
        { at: 4, line: L.gone, assert: "after the iframe unregisters, getTools() has no " + nm, want: lacks(nm) }],
    });
  }
}

// ============================ exposedTo-invalid-origins.https.html ===========================
{
  const loop = [
    ["/", "invalid", null], ["*", "invalid", null], ["https://example:bogus", "invalid", null],
    ["https://\ud800.com", "invalid", "'https://\\ud800.com' -> `invalid`: USVString conversion turns the lone surrogate into U+FFFD, which the host parser rejects"],
    ["http://example.com", "insecure", null],
    ["ftp://example.com", "insecure", "'ftp://example.com' -> `insecure`: it parses, but an ftp: URL's origin is opaque, so not potentially trustworthy"],
    ["about:blank", "insecure", "'about:blank' -> `insecure`: it parses, but its origin is opaque, so not potentially trustworthy"],
    ["about:srcdoc", "insecure", "'about:srcdoc' -> `insecure`, as for about:blank"],
    ["https://example.com", O(3), "'https://example.com' -> origin 3, a potentially trustworthy origin no document has"],
    ["http://localhost:3000", O(3), "'http://localhost:3000' -> origin 3: localhost is potentially trustworthy, and no document has that origin"]];
  const done = [];
  loop.forEach(([o, arg, proxy], i) => {
    const ok = arg.startsWith("origin:");
    const r = reg(ok ? `test_tool_0.${i}` : "test_tool_x", { description: "Test tool", behavior: "returnText", exposedTo: [arg] });
    C("exposedTo-invalid-origins.https.html", `registerTool() throws SecurityError for invalid or non-potentially-trustworthy origins like ${o} in exposedTo`, [26, 44], {
      ...(done.length ? { setup: [...done], setupNote: "the successful registrations of earlier iterations (never unregistered)" } : {}),
      trace: [r],
      checks: [ok ? { at: 0, line: 39, assert: `await registerTool(tool, {exposedTo: [${JSON.stringify(o)}]}) fulfils`, want: is("ok"), ...(proxy ? { proxy } : {}) }
        : { at: 0, line: 36, assert: `registerTool(tool, {exposedTo: [${JSON.stringify(o)}]}) rejects SecurityError`, want: is("err:SecurityError"), ...(proxy ? { proxy } : {}) }],
      notes: "The name is 'test_tool_' + Math.random(); the trace uses a fixed valid name.",
    });
    if (ok) done.push(r);
  });
  C("exposedTo-invalid-origins.https.html", "registerTool() with abort signal reason because signal is processed before `exposedTo`", [47, 54], {
    setup: [...done], setupNote: "the successful registrations of the loop (never unregistered)",
    trace: [abort(0), reg("name", { description: "description", behavior: "returnUndefined", signal: 0, exposedTo: ["insecure"] })],
    checks: [{ at: 1, line: 49, assert: "registerTool with AbortSignal.abort('aborted') and exposedTo ['about:blank#invalidOrigin'] rejects with the abort reason, not SecurityError", want: is("err:AbortError"),
      proxy: "AbortSignal.abort('aborted') -> a signal the trace aborts first, whose reason is the default AbortError, so 'rejects with the abort reason' reads err:AbortError (SecurityError if exposedTo were checked first); 'about:blank#invalidOrigin' -> `insecure` (it parses; its origin is opaque)" }],
  });
  C("exposedTo-invalid-origins.https.html", "Aborting a signal from a rejected registration must not unregister a later valid tool with the same name", [56, 95], {
    setup: [...done], setupNote: "the successful registrations of the loop (never unregistered)",
    trace: [reg("target_tool", { description: "Target tool", behavior: "returnText", signal: 1, exposedTo: ["insecure"] }),
      reg("target_tool", { description: "Target tool", behavior: "returnText", signal: 2 }), getTools(), abort(1),
      reg("target_tool", { description: "Target tool replacement", behavior: "returnText" }), exec("target_tool", "omitted")],
    checks: [
      { at: 0, line: 65, assert: "registerTool(target_tool, {signal: ac1, exposedTo: ['http://insecure.example']}) rejects SecurityError", want: is("err:SecurityError") },
      { at: 1, line: 69, assert: "await registerTool(target_tool, {signal: ac2}) fulfils", want: is("ok"), setup: true },
      { at: 2, line: 77, assert: "[tool] = getTools() is target_tool", want: field("target_tool", "description", { equals: "Target tool" }), setup: true },
      { at: 4, line: 89, assert: "after ac1.abort(), registering target_tool again rejects InvalidStateError", want: is("err:InvalidStateError") },
      { at: 5, line: 94, assert: "executeTool(tool) resolves with 'callback2'", want: is("result:hi"),
        proxy: "the tool returns the string 'callback2' -> model `returnText` ('hi')" }],
  });
}

// ============================ exposedTo-multiple-children.https.html =========================
C("exposedTo-multiple-children.https.html", "Multi-origin setup with mixed exposure lists", [15, 101], {
  trace: [reg("tool_b_to_c", { doc: 3, description: "Tool B exposed to C", input: "object", behavior: "returnText", signal: 9, exposedTo: [O(2)] }),
    getTools(), getTools({ doc: 2, fromOrigins: [O(1)] }), abort(9), getTools({ doc: 2, fromOrigins: [O(1)] })],
  checks: [
    { at: 0, line: 80, assert: "frame B's await registerTool(tool, {exposedTo: [C]}) fulfils (resources/iframe-register-tool.html)", want: is("ok"), setup: true },
    { at: 1, line: 62, assert: "the parent's getTools() returns []", want: count(0) },
    { at: 2, line: 69, assert: "frame C's getTools({fromOrigins: [B]}) returns B's tool, origin B (toolsAreEqual)", want: like("tool_b_to_c", { name: "tool_b_to_c", description: "Tool B exposed to C", inputSchema: { type: "object" }, outputSchema: null, origin: 1 }),
      proxy: "frame C (a child of the test page) -> document 2, which is nested in the same-origin document 1; getTools() walks every navigable of the tree, so where C sits doesn't change what it sees. inputSchema {type:'object', properties:...} -> model `object`" },
    { at: 4, line: 100, assert: "after B unregisters, frame C's getTools({fromOrigins: [B]}) returns []", want: count(0) }],
  notExpressible: [toolchange(58, "frame C receives toolchange on registration"), toolchange(94, "the parent receives no toolchange on unregistration"), toolchange(95, "frame C receives toolchange on unregistration")],
});

// ============================ getTools-filtering.https.html ==================================
C("getTools-filtering.https.html", "getTools() correctly filters returned tools by fromOrigins origins while preserving same-origin tools", [28, 96], {
  trace: [reg("parent_tool", { description: "Parent tool", behavior: "returnText", signal: 0 }),
    reg("iframe_tool_b", { doc: 3, description: "Tool from B exposed to parent", behavior: "returnText", signal: 9, exposedTo: [O(0)] }),
    reg("iframe_tool_c", { doc: 2, description: "Tool from C exposed to parent", behavior: "returnText", signal: 6, exposedTo: [O(0)] }),
    getTools(), getTools(), getTools({ fromOrigins: [O(1)] }), getTools({ fromOrigins: [O(1), O(2)] }), abort(0)],
  checks: [
    { at: 0, line: 31, assert: "await registerTool(parent_tool, {signal}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 80, assert: "iframe B's await registerTool(tool, {exposedTo: [self.origin]}) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 80, assert: "iframe C's await registerTool(tool, {exposedTo: [self.origin]}) fulfils", want: is("ok"), setup: true,
      proxy: "iframe C (a child of the test page) -> document 2, nested in the same-origin document 1; getTools() walks the whole tree" },
    { at: 3, line: 73, assert: "getTools() returns only parent_tool", want: names(["parent_tool"]) },
    { at: 4, line: 78, assert: "getTools({}) returns only parent_tool", want: names(["parent_tool"]), proxy: "getTools({}) -> getTools() with no fromOrigins; an omitted fromOrigins is the same empty list" },
    { at: 5, line: 83, assert: "getTools({fromOrigins: [B]}) returns iframe_tool_b, parent_tool", want: names(["iframe_tool_b", "parent_tool"]) },
    { at: 6, line: 89, assert: "getTools({fromOrigins: [B, C]}) returns iframe_tool_b, iframe_tool_c, parent_tool", want: names(["iframe_tool_b", "iframe_tool_c", "parent_tool"]) }],
});
C("getTools-filtering.https.html", "getTools() rejects with SecurityError if an insecure origin is supplied in fromOrigins", [98, 100], {
  trace: [getTools({ fromOrigins: ["insecure"] })],
  checks: [{ at: 0, line: 99, assert: "getTools({fromOrigins: ['http://insecure.com']}) rejects SecurityError", want: is("err:SecurityError") }],
});

// ============================ permissions-policy.https.html ==================================
const sameOriginNone = "a same-origin <iframe allow=\"tools 'none'\"> -> document 4, a cross-origin <iframe> without allow=\"tools\". The model has no same-origin document that is not allowed to use \"tools\"; the check that rejects is only whether the document is allowed, not its origin";
C("permissions-policy.https.html", "getTools() throws NotAllowedError in iframe when permissions policy is disabled", [61, 85], {
  trace: [getTools({ doc: 4 })],
  checks: [{ at: 0, line: 84, assert: "the cross-origin iframe's (no allow) getTools() rejects NotAllowedError", want: is("err:NotAllowedError") }],
});
C("permissions-policy.https.html", "executeTool() throws NotAllowedError in iframe when permissions policy is disabled", [87, 118], {
  trace: [reg("parent_tool", { description: "Parent tool", behavior: "returnText", signal: 0 }), getTools(), exec("parent_tool", "omitted", { doc: 4 }), abort(0)],
  checks: [
    { at: 0, line: 93, assert: "await registerTool(parent_tool, {signal}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 101, assert: "parent_tool is discovered", want: field("parent_tool", "name", { equals: "parent_tool" }), setup: true },
    { at: 2, line: 113, assert: "the iframe's executeTool(tool) rejects NotAllowedError", want: is("err:NotAllowedError"), proxy: sameOriginNone }],
});
C("permissions-policy.https.html", "registerTool() throws NotAllowedError in iframe when permissions policy is disabled", [120, 140], {
  trace: [reg("child_tool", { doc: 4, description: "Child tool", behavior: "returnText" })],
  checks: [{ at: 0, line: 131, assert: "the iframe's registerTool() rejects NotAllowedError", want: is("err:NotAllowedError"), proxy: sameOriginNone }],
});
C("permissions-policy.https.html", "getTools() throws NotAllowedError in same-origin iframe when permissions policy is disabled", [142, 158], {
  trace: [getTools({ doc: 4 })],
  checks: [{ at: 0, line: 153, assert: "the iframe's getTools() rejects NotAllowedError", want: is("err:NotAllowedError"), proxy: sameOriginNone }],
});
C("permissions-policy.https.html", "executeTool() rejects when target frame revokes exposedTo permission after getTools()", [197, 251], {
  trace: [reg("revocable_tool", { doc: 3, description: "Origin B revocable tool", behavior: "returnText", signal: 9, exposedTo: [O(0)] }),
    getTools({ fromOrigins: [O(1)] }), abort(9),
    reg("revocable_tool", { doc: 3, description: "Origin B private tool", behavior: "returnText", signal: 10, exposedTo: [] }),
    getTools({ doc: 3 }), exec("revocable_tool", "omitted", { call: 0 })],
  checks: [
    { at: 0, line: 80, assert: "the iframe's await registerTool(tool, {exposedTo: [self.origin]}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 222, assert: "getTools({fromOrigins: [B]}) finds revocable_tool", want: field("revocable_tool", "name", { equals: "revocable_tool" }) },
    { at: 3, line: 80, assert: "the iframe's re-registration with exposedTo [] fulfils", want: is("ok"), setup: true },
    { at: 4, line: 243, assert: "the iframe's getTools() returns one tool, revocable_tool", want: names(["revocable_tool"]) },
    { at: 5, line: 248, assert: "executeTool(the earlier Tool) rejects NotFoundError", want: is("err:NotFoundError") }],
  notes: "The earlier Tool's tool id was unregistered, so the spec rejects it as 'tool not found' before the exposure check (which would also reject, with NotFoundError, for the new tool).",
});

// ============================ executeTool-abort.https.html ===================================
C("executeTool-abort.https.html", "executeTool() provides a non-aborted default AbortSignal when called without options", [12, 31], {
  trace: [reg("default_signal_tool", { description: "Test default signal", behavior: "returnText", signal: 0 }), getTools(), exec("default_signal_tool", "omitted"), abort(0)],
  checks: [
    { at: 0, line: 17, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 28, assert: "executeTool(tool) resolves with 'success'", want: is("result:hi"),
      proxy: "the tool returns the string 'success' -> model `returnText` ('hi')" }],
  notExpressible: [{ line: "29-30", assert: "options.signal is a non-aborted AbortSignal", why: "the callback's own options.signal is not modelled" }],
});
C("executeTool-abort.https.html", "caller abort propagates to tool callback options.signal", [33, 122], {
  trace: [reg("abort_propagate_tool", { description: "Test abort propagation", behavior: "returnText", signal: 0 }), getTools(),
    conc([aExec("abort_propagate_tool", "live"), aCancel(0)]), abort(0)],
  checks: [
    { at: 0, line: 57, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, action: 0, line: 119, assert: "the execution rejects with 'custom cancellation reason'", want: is("err:AbortError"),
      proxy: customReason("'custom cancellation reason'") + ". " + afterStart + ". " + neverSettles },
    { at: 2, action: 1, line: 100, assert: "controller.abort() (the cancel itself)", want: is("ok"), setup: true }],
  notExpressible: [
    { line: "93-98, 110-117", assert: "one toolactivated and one toolcancel event at document.modelContext", why: "events are not modelled" },
    { line: 109, assert: "order of tool start, toolactivated, rejection, signal abort, toolcancel", why: "events and the callback's own signal are not modelled" },
    { line: "120-121", assert: "the callback's options.signal aborts with an AbortError", why: "the callback's own options.signal is not modelled" }],
});
C("executeTool-abort.https.html", "executeTool() with already-aborted tool synchronously rejects", [124, 145], {
  trace: [reg("already_aborted_tool", { description: "Test already aborted signal", behavior: "returnText", signal: 0 }), getTools(),
    conc([aExec("already_aborted_tool", "aborted")]), abort(0)],
  checks: [
    { at: 0, line: 128, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, action: 0, line: 144, assert: "executeTool(tool, {}, {signal: AbortSignal.abort('already aborted')}) rejects with 'already aborted'", want: is("err:AbortError"),
      proxy: "AbortSignal.abort('already aborted') -> an `aborted` execution signal, whose reason is the default AbortError; executeTool() returns a promise rejected with the signal's abort reason (index.bs L1140-L1141). The tool (t.unreached_func) -> `returnText`; it never runs either way" }],
  notExpressible: [{ line: 143, assert: "the rejection is already observable after one microtask", why: "the oracle reports outcomes, not timing. The model rejects in executeTool()'s method steps (`syncAction`), which is what the timing checks" }],
});
C("executeTool-abort.https.html", "executeTool() promise remains rejected even if tool callback resolves after abort", [147, 180], {
  trace: [reg("async_resolve_after_abort_tool", { description: "Test resolving promise after abort", behavior: "returnText", signal: 0 }), getTools(),
    conc([aExec("async_resolve_after_abort_tool", "live"), aCancel(0)]), abort(0)],
  checks: [
    { at: 0, line: 153, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, action: 0, line: 172, assert: "executeTool() then controller.abort() in the same script: rejects AbortError even if the tool resolves", want: is("err:AbortError"),
      proxy: "the tool resolves 'late resolved value' once its options.signal aborts -> model `returnText`, which resolves; the cancelled call rejects whatever the callback does" }],
  notExpressible: [{ line: "178-179", assert: "the callback's own promise resolves 'late resolved value'", why: "the callback's own options.signal is not modelled" }],
});
C("executeTool-abort.https.html", "concurrent executions of the same tool have independent AbortSignals", [182, 233], {
  trace: [reg("concurrent_tool", { description: "Test concurrent executions", behavior: "returnText", signal: 0 }), getTools(),
    conc([aExec("concurrent_tool", "live"), aExec("concurrent_tool", "live"), aCancel(0)]), abort(0)],
  checks: [
    { at: 0, line: 193, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, action: 0, line: 225, assert: "c1.abort('cancel 1'): execPromise1 rejects with 'cancel 1'", want: is("err:AbortError"),
      proxy: customReason("'cancel 1'") + ". " + afterStart },
    { at: 2, action: 1, line: 232, assert: "execPromise2 resolves with 'exec2 result'", want: is("result:hi"),
      proxy: "the first execution never settles and the second resolves 'exec2 result' -> model `returnText` for both ('hi'); the first is cancelled, so only the second's result is seen; the WPT assertion is that the result is the returned string itself, so 'hi'" }],
  notExpressible: [{ line: "228-229", assert: "execution 1's options.signal is aborted and execution 2's is not", why: "the callback's own options.signal is not modelled" }],
});

// ============================ executeTool-signal-cross-origin.https.html =====================
for (const [sub, lines, nm, desc, l, reason, extraProxy, ne] of [
  ["caller abort in parent document propagates to options.signal in cross-origin iframe tool", [15, 73], "cross_origin_iframe_tool", "Cross origin tool in iframe", 68, "'parent cross-origin abort reason'", "",
    [{ line: "70-72", assert: "the iframe tool's options.signal aborts with an AbortError, and toolcancel fires in the iframe", why: "the callback's own options.signal and events are not modelled" }]],
  ["other frame aborting an AbortController passed to executeTool() cancels target execution and fires toolcancel", [128, 194], "third_frame_cancel_tool", "Cross origin tool cancelled by third frame signal", 190, "'aborted from third frame'",
    ". The AbortController comes from a third (same-origin) iframe's realm and the test page aborts it -> a signal of the caller's; the model has no realms, and executeTool()'s abort steps don't depend on the signal's realm",
    [{ line: "192-193", assert: "the iframe tool's options.signal aborts with an AbortError, and toolcancel fires in the iframe", why: "the callback's own options.signal and events are not modelled" }]]]) {
  C("executeTool-signal-cross-origin.https.html", sub, lines, {
    trace: [reg(nm, { doc: 3, description: desc, behavior: "returnText", signal: 9, exposedTo: [O(0)] }), getTools({ fromOrigins: [O(1)] }),
      conc([aExec(nm, "live"), aCancel(0)])],
    checks: [
      { at: 0, line: 80, assert: "the iframe's await registerTool(tool, {exposedTo: [self.origin]}) fulfils (resources/iframe-register-tool.html)", want: is("ok"), setup: true },
      { at: 1, line: l === 68 ? 44 : 163, assert: "getTools({fromOrigins: [REMOTE]}) finds the tool", want: field(nm, "name", { equals: nm }), setup: true },
      { at: 2, action: 0, line: l, assert: `executeTool(tool, {}, {signal}) rejects with ${reason} after controller.abort()`, want: is("err:AbortError"),
        proxy: customReason(reason) + ". " + afterStart + ". The iframe tool hangs forever (hangsForeverAndReportsAbort) -> model `returnText`" + extraProxy }],
    notExpressible: ne,
  });
}

// ============================ unregister-during-executeTool.https.html =======================
const selfUnreg = (who) => `${who} unregisters the tool while its callback is pending -> model \`unregisterSelf\`, whose callback aborts its own registration signal and then resolves with its input. Either way the unregistration comes after "invoke the execute callback" has started, which the spec's note says doesn't cancel the execution`;
C("unregister-during-executeTool.https.html", "Pending executeTool() Promise resolves successfully when the target cross-origin tool is unregistered mid-execution", [25, 97], {
  trace: [reg("endless_tool", { doc: 3, description: "Endless tool in iframe", behavior: "unregisterSelf", signal: 9, exposedTo: [O(0)] }),
    getTools({ fromOrigins: [O(1)] }), exec("endless_tool"), getTools({ fromOrigins: [O(1)] })],
  checks: [
    { at: 0, line: 80, assert: "the iframe's await registerTool(tool, {exposedTo: [self.origin]}) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 63, assert: "the tool is visible to the parent", want: field("endless_tool", "name", { equals: "endless_tool" }), setup: true },
    { at: 2, line: 96, assert: "the pending execution resolves with the tool's result", want: is("result:{}"),
      proxy: selfUnreg("The iframe's message handler") + ". The tool resolves 'delayed_result'; `unregisterSelf` resolves with the omitted input, so the result reads '{}'. This hides the #361 half of L96: WPT also expects the string 'delayed_result' back without JSON encoding" },
    { at: 3, line: 90, assert: "getTools({fromOrigins: [REMOTE]}) no longer returns the tool", want: count(0),
      proxy: "WPT calls getTools() after the unregistration and before the execution settles; the trace calls it after, when the tool map is the same" }],
  notExpressible: [{ line: 74, assert: "the tool's options.signal is not aborted by the unregistration", why: "the callback's own options.signal is not modelled" }],
});
C("unregister-during-executeTool.https.html", "Pending executeTool() Promise resolves successfully when target same-document tool is unregistered mid-execution", [99, 134], {
  trace: [reg("same_doc_unregister_tool", { description: "Test unregister during exec in same doc", behavior: "unregisterSelf", signal: 0 }), getTools(), exec("same_doc_unregister_tool"), getTools()],
  checks: [
    { at: 0, line: 106, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 133, assert: "the pending execution resolves with the tool's result", want: is("result:{}"),
      proxy: selfUnreg("The test's regController.abort()") + ". The tool returns 'same_doc_result'; `unregisterSelf` resolves with the omitted input, so the result reads '{}'. This hides the #361 half of L133" },
    { at: 3, line: 128, assert: "getTools() no longer returns the tool", want: count(0),
      proxy: "WPT calls getTools() before the execution settles; the trace calls it after, when the tool map is the same" }],
  notExpressible: [{ line: 110, assert: "the tool's options.signal is not aborted by the unregistration", why: "the callback's own options.signal is not modelled" }],
});
C("unregister-during-executeTool.https.html", "executeTool() cancellation propagates to options.signal even when tool synchronously unregistered itself inside execute()", [136, 165], {
  trace: [reg("sync_unregister_then_abort_tool", { description: "Synchronously unregisters itself during execute(), then gets cancelled", behavior: "unregisterSelf", signal: 0 }), getTools(),
    conc([aExec("sync_unregister_then_abort_tool", "live"), aCancel(0)]), getTools()],
  checks: [
    { at: 0, line: 143, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, action: 0, line: 163, assert: "execController.abort('caller_cancelled') after the tool unregistered itself: rejects with 'caller_cancelled'", want: is("err:AbortError"),
      proxy: customReason("'caller_cancelled'") + ". " + afterStart + ". The tool aborts regController and returns a promise that never settles -> `unregisterSelf`, which aborts its registration signal and then resolves; the cancelled call rejects either way" }],
  notExpressible: [{ line: 164, assert: "the callback's options.signal aborts", why: "the callback's own options.signal is not modelled" }],
});

// ============================ executeTool-unregister-resolution-race.https.html ==============
C("executeTool-unregister-resolution-race.https.html", "executeTool resolves successfully even when tool is unregistered synchronously after its promise resolves", [11, 37], {
  trace: [reg("racy_tool", { description: "a racy tool", behavior: "unregisterSelf", signal: 0 }), getTools(), exec("racy_tool"), getTools()],
  checks: [
    { at: 0, line: 14, assert: "await registerTool(..., {signal}) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 36, assert: "executeTool(tool) resolves with the JSON of the returned object", want: is("result:{}"),
      proxy: "the callback resolves {status:'resolved'} and then aborts its own registration signal -> `unregisterSelf`, which aborts first and then resolves with the received {}; both happen inside the callback, after \"invoke the execute callback\" started. WPT's '{\"status\":\"resolved\"}' becomes '{}' (JSON either way)" }],
  notes: "The trailing getTools() shows the tool did unregister itself (it is not a WPT assertion).",
});

// ============================ executeTool-events.https.html ==================================
C("executeTool-events.https.html", "toolactivated and toolcancel events are dispatched on document.modelContext during tool execution and cancellation", [9, 74], {
  trace: [reg("slow", { description: "slow tool", behavior: "returnText", signal: 0 }), getTools(), conc([aExec("slow", "live"), aCancel(0)]), abort(0)],
  checks: [
    { at: 0, line: 29, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, action: 0, line: 54, assert: "controller.abort(): executeTool() rejects AbortError", want: is("err:AbortError"), proxy: afterStart + ". " + neverSettles }],
  notExpressible: [{ line: "41-52, 59-72", assert: "toolactivated and toolcancel events and their members", why: "events are not modelled" }],
});
C("executeTool-events.https.html", "toolactivated is dispatched at the ModelContext of the tool target document", [76, 108], {
  trace: [reg("iframe_tool", { doc: 1, description: "Tool registered in a same-origin child document", behavior: "returnText" }), getTools(), exec("iframe_tool")],
  checks: [
    { at: 0, line: 84, assert: "await iframeModelContext.registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 100, assert: "iframe_tool is visible to the parent document", want: field("iframe_tool", "name", { equals: "iframe_tool" }) },
    { at: 2, line: 102, assert: "executeTool(tool, {}) resolves with 'iframe result'", want: is("result:hi"),
      proxy: "the tool returns the string 'iframe result' -> model `returnText` ('hi'); the WPT assertion is that the result is the returned string itself. {} serializes like the omitted input" }],
  notExpressible: [{ line: "104-107", assert: "toolactivated fires at the target document's ModelContext, not the caller's", why: "events are not modelled" }],
});
C("executeTool-events.https.html", "toolcancel is dispatched at the ModelContext of the tool target document", [110, 152], {
  trace: [reg("iframe_slow_tool", { doc: 1, description: "Slow tool registered in a same-origin child document", behavior: "returnText" }), getTools(),
    conc([aExec("iframe_slow_tool", "live"), aCancel(0)])],
  checks: [
    { at: 0, line: 118, assert: "await iframeModelContext.registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 1, line: 139, assert: "iframe_slow_tool is visible to the parent document", want: field("iframe_slow_tool", "name", { equals: "iframe_slow_tool" }) },
    { at: 2, action: 0, line: 143, assert: "executeTool(tool, {}, {signal}) then controller.abort(): rejects AbortError", want: is("err:AbortError"), proxy: neverSettles }],
  notExpressible: [{ line: "148-151", assert: "toolcancel fires at the target document's ModelContext, not the caller's", why: "events are not modelled" }],
});

// ============================ tool-cancel-event.https.html ===================================
C("/tool-cancel-event.https.html", "ontoolcancel is invoked when a tool invocation is canceled", [49, 104], {
  trace: [reg("onevent_tool", { description: "Tool used to trigger ontoolcancel", behavior: "returnText", signal: 0 }), getTools(),
    conc([aExec("onevent_tool", "live"), aCancel(0)]), conc([aExec("onevent_tool", "live"), aCancel(0)]), abort(0)],
  checks: [
    { at: 0, line: 62, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, action: 0, line: 84, assert: "first executeTool() then controller.abort(): rejects AbortError", want: is("err:AbortError"), proxy: neverSettles },
    { at: 3, action: 0, line: 84, assert: "second executeTool() then controller.abort(): rejects AbortError", want: is("err:AbortError"), proxy: neverSettles }],
  notExpressible: [{ line: "50, 57, 92-94, 97, 102", assert: "ontoolcancel reflects the handler and is invoked exactly once", why: "events are not modelled" }],
});

// ============================ same-origin-iframe-registerTool-regression.https.html ==========
C("same-origin-iframe-registerTool-regression.https.html", "registerTool() does not reject in connected same-origin iframe navigated away of about:blank", [10, 26], {
  trace: [reg("connected_tool", { doc: 1, description: "Tool registered in connected frame", behavior: "returnText" })],
  checks: [{ at: 0, line: 21, assert: "the same-origin iframe's await registerTool(...) fulfils", want: is("ok"),
    proxy: "the iframe's document, loaded after its initial about:blank -> document 1. The model has no navigation; the call is made in the loaded document, which is what the assertion needs" }],
});

// ---- out-of-scope inventory -------------------------------------------------------------------
const fileReason = {
  "idlharness.https.window.js": "IDL shape (interfaces, members, [SecureContext]); the model has no IDL surface",
  "tool-activated-event.https.html": "events (ToolActivatedEvent, ontoolactivated)",
  "tool-cancel-event.https.html": "events (ToolCancelEvent, ontoolcancel)",
  "imperative/detached-frame-executeTool.https.html": "detached document (fully-active checks); the model's document is always fully active",
  "imperative/detached-frame-getTools.https.html": "detached document (fully-active checks)",
  "imperative/detached-frame-modelContext.https.html": "detached document (fully-active checks)",
  "imperative/detached-frame-registerTool.https.html": "detached document (fully-active checks)",
  "imperative/detached-frame-waitForToolsUntil.https.html": "non-modelled API waitForToolsUntil() (not in the spec IDL at 14b6d53), detached document",
  "imperative/executeTool-abort.https.html": "a callback that aborts its caller's execution signal (the model's callbacks only settle or unregister their own tool), the callback's own options.signal, toolcancel",
  "imperative/executeTool-across-trees.https.html": "multiple frame trees (window.open): a document in another traversable",
  "imperative/executeTool-caller-navigate-abort.https.html": "navigation/detach of the caller, execution signal, toolcancel",
  "imperative/executeTool-detach-toolactivated.https.html": "events, detach during execution, iframes",
  "imperative/executeTool-detach-toolcancel.https.html": "events, detach during cancellation, iframes",
    "imperative/executeTool-reentrant-cancellation.https.html": "execution signal / cancellation, re-entrant execution, iframe detach",
  "imperative/executeTool-signal-cross-origin.https.html": "asserts only on the callback's own options.signal and toolcancel, which are not modelled",
  "imperative/executeTool-target-detachment.https.html": "detach of the target frame, execution signal",
  "imperative/executeTool-target-navigation.https.html": "navigation of the target document, iframes",
    "imperative/exposedTo-cross-origin-child.https.html": "asserts only on toolchange events",
          "imperative/exposedTo-window-open.https.html": "multiple frame trees (window.open): a document in another traversable",
    "imperative/initial-about-blank-replacement-register-tool.https.html": "navigation / document replacement, iframes",
  "imperative/initial-about-blank-replacement-removes-tools.https.html": "navigation / document replacement, iframes",
  "imperative/initial-about-blank-shared-tool.https.html": "navigation / document replacement, iframes",
  "imperative/javascript-url-document-replacement.https.html": "navigation / document replacement, iframes",
  "imperative/model_context.https.html": "document without a browsing context (fully-active checks), iframes",
  "imperative/non-secure.html": "secure-context exposure ([SecureContext])",
  "imperative/opaque-origin-tools.https.html": "opaque origins, sandboxed iframes, popups",
  "imperative/permissions-policy.https.html": "navigation of an iframe to an origin its allow attribute does not cover",
  "imperative/register-tool-input-schema-registers-same-name.https.html": "page script run by toJSON() during registerTool() (the model's toJSON runs no script, so it omits the second duplicate-name check)",
  "imperative/register_tool_toolchange.https.html": "events (toolchange ordering)",
    "imperative/unregister-during-executeTool.https.html": "re-entrant executeTool() from inside a callback (the model's callbacks only settle or unregister their own tool)",
  "imperative/wait-for-tools-until.https.html": "non-modelled API waitForToolsUntil() (not in the spec IDL at 14b6d53)",
};
const subReason = {
  "imperative/model_context.https.html\u0000'document.modelContext instanceof ModelContext'": "interface identity (instanceof); the model has no IDL surface",
  "imperative/model_context.https.html\u0000'document.modelContext SameObject'": "[SameObject] identity; the model has no IDL surface",
  "imperative/permissions-policy.https.html\u0000'resumeTool() throws NotAllowedError in iframe when permissions policy is disabled'": "non-modelled API resumeTool() (not in the spec IDL at 14b6d53), permissions policy",
  "imperative/permissions-policy.https.html\u0000'waitForToolsUntil() throws NotAllowedError in iframe when permissions policy is disabled'": "non-modelled API waitForToolsUntil() (not in the spec IDL at 14b6d53), permissions policy",
};
const expand = {
  "imperative/exposedTo-invalid-origins.https.html:26": ["/", "*", "https://example:bogus", "https://\ud800.com", "http://example.com", "ftp://example.com", "about:blank", "about:srcdoc", "https://example.com", "http://localhost:3000"]
    .map((o) => `registerTool() throws SecurityError for invalid or non-potentially-trustworthy origins like ${o} in exposedTo`),
  "imperative/model_context.https.html:21": ["active document first", "inactive document first"].map((o) => `createHTMLDocument().modelContext rejects tool operations with InvalidStateError, with ${o}`),
  "imperative/executeTool-caller-navigate-abort.https.html:28": ["same-origin", "cross-origin"].map((o) => `executeTool() aborts target signal and fires toolcancel when the invoker document (${o}) navigates away`),
  "imperative/executeTool-caller-navigate-abort.https.html:92": ["same-origin", "cross-origin"].map((o) => `executeTool() aborts target signal and fires toolcancel when the invoker frame (${o}) is detached from the DOM`),
  "declarative/executeTool-respondWith-unserializable.https.html:41": ["a Symbol", "an object with a BigInt property", "an object whose toJSON() throws", "an object with a throwing getter"].map((d) => `Declarative tool executeTool() rejects when respondWith() receives ${d}`),
  "declarative/no-frame-documents.https.html:55": ["adoptNode", "cloneNode", "importNode"].map((o) => `${o} transfers a frameless form into an active document and registers a working tool`),
};
// Translated by hand above; the extractor's entries for these files are replaced.
const handled = new Set(cases.map((c) => c.file.replace(/^webmcp\//, "")));
// A subtest name that is string literals joined with `+`, decoded without evaluating anything
// from the (untrusted) checkout; anything else (template literals) is kept as source text.
function unquote(src) {
  if (/^`[^`$\\]*`$/.test(src)) return src.slice(1, -1);
  const toks = src.match(/'(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"/g);
  if (!toks || src.replace(/'(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"/g, "").replace(/[\s+]/g, "") !== "") return src;
  return toks.map((t) => t[0] === '"' ? JSON.parse(t)
    : JSON.parse('"' + t.slice(1, -1).replace(/\\'/g, "'").replace(/(^|[^\\])"/g, '$1\\"') + '"')).join("");
}
const out = [];
const matched = new Set();
const crash = new Set(["imperative/abort-signal-after-iframe-removal-crash.https.html", "imperative/cancel-reentrancy-crash.https.html",
  "imperative/register-tool-input-schema-removes-iframe-crash.https.html", "imperative/executeTool-same-document-navigation-crash.https.html",
  "imperative/wait-for-tools-until-detach-crash.https.html"]);
for (const f of raw) {
  if (!/\.(html|js)$/.test(f.file) || f.file.includes("resources/")) continue;
  const file = "webmcp/" + f.file;
  if (crash.has(f.file)) { out.push({ file, subtest: "(crash test: no subtests; passes if the page finishes without crashing)", lines: null, scope: "out", reason: "crash test with iframe removal / navigation / re-entrancy" }); continue; }
  if (f.file === "idlharness.https.window.js") { out.push({ file, subtest: "(idl_test: generated IDL subtests)", lines: [8, 12], scope: "out", reason: fileReason[f.file] }); continue; }
  for (const s of f.subtests) {
    const key = f.file + ":" + s.line;
    const nameList = expand[key] || [unquote(s.name)];
    for (const name of nameList) {
      if (handled.has(f.file) && inScopeNames.has(f.file + "\u0000" + name)) { matched.add(f.file + "\u0000" + name); continue; }
      if (f.file === "imperative/register_tool_invalid_json_schema.https.html") continue; // all translated above
      if (f.file === "imperative/executeTool-error-window-onerror.https.html") continue;   // all translated above
      const reason = subReason[f.file + "\u0000" + s.name] || fileReason[f.file] || (f.file.startsWith("declarative/") ? "declarative API (form-based tools), which the spec text at 14b6d53 does not define" : null);
      if (!reason) throw new Error("no reason for " + key + " " + name);
      out.push({ file, subtest: name, lines: [s.line, s.endLine], scope: "out", reason });
    }
  }
}

for (const k of inScopeNames)
  if (!matched.has(k) && !/register_tool_invalid_json_schema|executeTool-error-window-onerror/.test(k))
    throw new Error("translated subtest not in the inventory: " + k.replace("\u0000", " / "));

// ---- resolve execute ops against the oracle's own getTools() results -------------------------
function runOracle(ops) {
  if (!ops.length) return [];
  return JSON.parse(execFileSync(oracle, { input: JSON.stringify(ops) + "\n" }).toString().trim().split("\n")[0]);
}
// The names each getTools() call of `ops` returned, numbered as the oracle numbers calls: a
// rejected call counts and returns none, and each getTools action of a `concurrent` counts.
function toolLists(ops, res) {
  const listed = (o) => o.startsWith("tools:") ? o.slice(6).split(";").filter(Boolean).map((t) => t.split("|")[0]) : [];
  const lists = [];
  ops.forEach((o, i) => {
    if (o.op === "getTools") lists.push(listed(res[i]));
    if (o.op === "concurrent") {
      const alts = res[i].startsWith("any:") ? JSON.parse(res[i].slice(4)) : [res[i]];
      const acts = alts.map((a) => JSON.parse(a.slice(4)));
      o.actions.forEach((a, k) => {
        if (a.act !== "getTools") return;
        if (new Set(acts.map((x) => x[k])).size > 1) throw new Error("getTools action whose result depends on the order: " + JSON.stringify(o));
        lists.push(listed(acts[0][k]));
      });
    }
  });
  return lists;
}
function indexOf(lists, call, tool) {
  const c = call === "last" ? lists.length - 1 : call;
  const index = (lists[c] || []).indexOf(tool);
  if (index < 0) throw new Error("tool " + tool + " not in getTools() call " + c);
  return { call: c, index };
}
// Each op that names a tool is resolved against the oracle's run of the ops before it.
function resolve(setup, trace) {
  const outOps = [];
  for (const o of [...setup, ...trace]) {
    if (o.op === "execute") {
      const lists = toolLists(outOps, runOracle(outOps));
      const { doc, ...rest } = o;
      outOps.push({ op: "execute", ...indexOf(lists, o.call, o.tool), input: o.input, ...(doc ? { doc } : {}) });
    } else if (o.op === "concurrent" && o.actions.some((a) => a.act === "execute")) {
      const lists = toolLists(outOps, runOracle(outOps));
      outOps.push({ ...o, actions: o.actions.map((a) => a.act !== "execute" ? a
        : { act: "execute", ...indexOf(lists, a.call, a.tool), input: a.input, signal: a.signal }) });
    } else outOps.push(o);
  }
  return { setup: outOps.slice(0, setup.length), trace: outOps.slice(setup.length) };
}
for (const c of cases) {
  const r = resolve(c.setup || [], c.trace);
  c.setup = r.setup; c.trace = r.trace;
  if (c.extra) { const e = resolve([], c.extra.trace); c.extra.trace = e.trace; }
  if (!c.setup.length) delete c.setup;
}

// ---- classifications of the disagreements (see wpt/README.md) --------------------------------
const issue361 = { kind: "spec-vs-wpt", ref: "#361",
  spec: "spec.bs 'invoke the execute callback', fulfilled branch: 'Let serializedResult be the result of serializing a JavaScript value to a JSON string given v' (14b6d53 L618-622)",
  summary: "WPT expects the tool's string result back unchanged; the spec JSON-serializes it, so a tool returning 'hi' gives '\"hi\"'" };
for (const c of cases) for (const k of [...c.checks, ...(c.extra ? c.extra.checks : [])])
  if (k.want.outcome && k.want.outcome.startsWith("result:") && k.want.outcome !== "result:{}" && k.want.outcome !== "result:[]") k.expectDisagree = issue361;

const doc = {
  about: "Hand translation of the web-platform-tests webmcp/ subtests into traces for the Lean model's oracle (Main.lean). Scored by tools/wpt-score.cjs; method and caveats in wpt/README.md.",
  wpt: { repo: "https://github.com/web-platform-tests/wpt", commit: WPT_COMMIT, date: "2026-11-22" },
  spec: { repo: "https://github.com/webmachinelearning/webmcp", commit: "14b6d53" },
  format: {
    trace: "ops exactly as the oracle reads them; `setup` (if present) reproduces state left by earlier subtests in the same file and is run first, its outcomes unchecked",
    checks: "`at` indexes the trace (not setup), and `action` the action of a `concurrent` op; `want` is what the WPT assertion requires: {outcome} exact oracle outcome string, {resolves} any result, {names} tool names in order, {count}, {lacks} no tool of that name, {tool, like} helpers.js toolsAreEqual() (origin is the model origin of the Tool's source document), or {tool, field} with {equals}|{isNull}|{notNull}|{json}|{path, equals}. Where the model allows several outcomes, a check agrees only if every one satisfies it",
    setup: "a check with `setup: true` is incidental (an awaited call the test needs to succeed) and does not by itself make a subtest count as expressible",
    proxy: "the model value substituted for a WPT value it cannot express, and why the substitution reaches the same spec steps",
    extra: "a second trace for the same subtest, when one tool cannot show two things at once",
    expectDisagree: "the recorded classification of a check known to disagree; the scorer flags any disagreement without one, and any classified check that now agrees",
  },
  subtests: [...cases, ...out].sort((a, b) => a.file < b.file ? -1 : a.file > b.file ? 1 : (a.lines?.[0] ?? 0) - (b.lines?.[0] ?? 0)),
};
// One op, check or inventory row per line, so the file reads (and diffs) like a table.
function fmt(v, ind = "") {
  const c = JSON.stringify(v);
  if (c.length <= 100 || (v && !Array.isArray(v) && typeof v === "object" && (v.op || "at" in v || "why" in v))) return c;
  const i2 = ind + "  ";
  if (Array.isArray(v)) return "[\n" + v.map((x) => i2 + fmt(x, i2)).join(",\n") + "\n" + ind + "]";
  if (v && typeof v === "object") return "{\n" + Object.entries(v).filter(([, x]) => x !== undefined).map(([k, x]) => i2 + JSON.stringify(k) + ": " + fmt(x, i2)).join(",\n") + "\n" + ind + "}";
  return c;
}
fs.writeFileSync(outPath, fmt(doc) + "\n");
console.log(`${cases.length} translated, ${out.length} out of scope`);
