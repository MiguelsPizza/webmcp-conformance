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
function reg(name, o = {}) {
  return {
    op: "register", name,
    title: o.title ?? null,
    description: o.description === undefined ? "d" : o.description,
    inputSchema: o.input ?? "absent", outputSchema: o.output ?? "absent",
    annotations: o.ann ?? null, behavior: o.behavior ?? "echo",
    signal: o.signal ?? null,
  };
}
const regAbortSync = (name, signal, o = {}) => ({ ...reg(name, o), op: "registerAbortSync", signal });
const abort = (signal) => ({ op: "abort", signal });
const getTools = () => ({ op: "getTools" });
// `tool` is resolved to an index into the most recent getTools() result below.
const exec = (tool, input = "omitted") => ({ op: "execute", call: "last", tool, input });

// ---- expectation builders (what the WPT assertion requires, in oracle outcome form) --------
const is = (outcome) => ({ outcome });
const names = (list) => ({ names: list });
const count = (n) => ({ count: n });
const field = (tool, f, extra) => ({ tool, field: f, ...extra });

const cases = [];   // translated subtests
const inScopeNames = new Set();
function C(file, subtest, lines, body) {
  inScopeNames.add(file + "\u0000" + subtest);
  cases.push({ file: "webmcp/imperative/" + file, subtest, lines, scope: "in", ...body });
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
  trace: [], checks: [],
  notExpressible: [{ line: 29, assert: "promise rejects with exactly the Error passed to controller.abort(error)",
    why: "the model's signals abort only with the default reason (an AbortError DOMException); a custom abort reason is not in its value set" }],
});
C("register_tool_signal.https.html", "register tool promise rejects when signal is already aborted", [32, 36], {
  trace: [], checks: [],
  notExpressible: [{ line: 35, assert: "promise rejects with exactly 'aborted' (AbortSignal.abort('aborted'))",
    why: "custom abort reason, as above; the model would say err:AbortError for an already-aborted default-reason signal" }],
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

// ============================ exposedTo-invalid-origins.https.html (last subtest) ==========
C("exposedTo-invalid-origins.https.html", "Aborting a signal from a rejected registration must not unregister a later valid tool with the same name", [56, 95], {
  setup: [reg("test_tool_0.25", { description: "Test tool", behavior: "returnText" }), reg("test_tool_0.75", { description: "Test tool", behavior: "returnText" })],
  setupNote: "the two successful registrations of earlier subtests ('test_tool_' + Math.random(), exposedTo a valid origin); exposedTo is dropped, which does not change what this document's getTools() returns",
  trace: [reg("target_tool", { description: "", behavior: "returnText", signal: 1 }),
    reg("target_tool", { description: "Target tool", behavior: "returnText", signal: 2 }), getTools(), abort(1),
    reg("target_tool", { description: "Target tool replacement", behavior: "returnText" }), exec("target_tool", "omitted")],
  checks: [
    { at: 1, line: 69, assert: "await registerTool(target_tool, {signal: ac2}) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 77, assert: "[tool] = getTools() is target_tool", want: field("target_tool", "description", { equals: "Target tool" }), setup: true },
    { at: 4, line: 89, assert: "after ac1.abort(), registering target_tool again rejects InvalidStateError", want: is("err:InvalidStateError") },
    { at: 5, line: 94, assert: "executeTool(tool) resolves with 'callback2'", want: is("result:hi"),
      proxy: "the tool returns the string 'callback2' -> model `returnText` ('hi')" }],
  notExpressible: [{ line: 65, assert: "the first registration rejects SecurityError (exposedTo: ['http://insecure.example'])",
    why: "exposedTo is out of the model's scope. The trace makes the first registration (with signal ac1) fail on the empty-description step instead, which also returns before the abort steps are added, so aborting ac1 must not touch target_tool either way" }],
});

// ============================ executeTool-abort.https.html (first subtest) =================
C("executeTool-abort.https.html", "executeTool() provides a non-aborted default AbortSignal when called without options", [12, 31], {
  trace: [reg("default_signal_tool", { description: "Test default signal", behavior: "returnText", signal: 0 }), getTools(), exec("default_signal_tool", "omitted"), abort(0)],
  checks: [
    { at: 0, line: 17, assert: "await registerTool(...) fulfils", want: is("ok"), setup: true },
    { at: 2, line: 28, assert: "executeTool(tool) resolves with 'success'", want: is("result:hi"),
      proxy: "the tool returns the string 'success' -> model `returnText` ('hi')" }],
  notExpressible: [{ line: "29-30", assert: "options.signal is a non-aborted AbortSignal", why: "the execution signal is out of the model's scope" }],
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
  "imperative/executeTool-abort.https.html": "execution signal / cancellation, toolactivated/toolcancel events",
  "imperative/executeTool-across-trees.https.html": "multiple frame trees (window.open)",
  "imperative/executeTool-caller-navigate-abort.https.html": "navigation/detach of the caller, execution signal, toolcancel",
  "imperative/executeTool-detach-toolactivated.https.html": "events, detach during execution, iframes",
  "imperative/executeTool-detach-toolcancel.https.html": "events, detach during cancellation, iframes",
  "imperative/executeTool-events.https.html": "events (toolactivated/toolcancel), execution signal, iframes",
  "imperative/executeTool-reentrant-cancellation.https.html": "execution signal / cancellation, re-entrant execution, iframe detach",
  "imperative/executeTool-signal-cross-origin.https.html": "execution signal, cross-origin iframes",
  "imperative/executeTool-target-detachment.https.html": "detach of the target frame, execution signal",
  "imperative/executeTool-target-navigation.https.html": "navigation of the target document, iframes",
  "imperative/executeTool-unregister-resolution-race.https.html": "unregistration from inside a running callback (interleaving the model does not express)",
  "imperative/exposedTo-cross-origin-child.https.html": "cross-origin iframes, exposedTo, toolchange events",
  "imperative/exposedTo-defaults-cross-origin.https.html": "cross-origin iframes, exposedTo defaults",
  "imperative/exposedTo-defaults-same-origin.https.html": "iframes (multi-document), exposedTo defaults",
  "imperative/exposedTo-invalid-origins.https.html": "exposedTo origin validation (SecurityError)",
  "imperative/exposedTo-multiple-children.https.html": "cross-origin iframes, exposedTo",
  "imperative/exposedTo-window-open.https.html": "multiple frame trees (window.open), exposedTo",
  "imperative/getTools-filtering.https.html": "cross-origin iframes, getTools({fromOrigins}) filtering and validation",
  "imperative/initial-about-blank-replacement-register-tool.https.html": "navigation / document replacement, iframes",
  "imperative/initial-about-blank-replacement-removes-tools.https.html": "navigation / document replacement, iframes",
  "imperative/initial-about-blank-shared-tool.https.html": "navigation / document replacement, iframes",
  "imperative/javascript-url-document-replacement.https.html": "navigation / document replacement, iframes",
  "imperative/model_context.https.html": "document without a browsing context (fully-active checks), iframes",
  "imperative/non-secure.html": "secure-context exposure ([SecureContext])",
  "imperative/opaque-origin-tools.https.html": "opaque origins, sandboxed iframes, popups",
  "imperative/permissions-policy.https.html": "permissions policy (plus non-modelled resumeTool()/waitForToolsUntil()), cross-origin iframes",
  "imperative/register-tool-input-schema-registers-same-name.https.html": "page script run by toJSON() during registerTool() (the model's toJSON runs no script, so it omits the second duplicate-name check)",
  "imperative/register_tool_toolchange.https.html": "events (toolchange ordering)",
  "imperative/same-origin-iframe-registerTool-regression.https.html": "iframes",
  "imperative/unregister-during-executeTool.https.html": "unregistration while an execution is pending (interleaving), execution signal, iframes",
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
      if (handled.has(f.file) && inScopeNames.has(f.file.replace(/^imperative\//, "") + "\u0000" + name)) continue;
      if (f.file === "imperative/register_tool_invalid_json_schema.https.html") continue; // all translated above
      if (f.file === "imperative/executeTool-error-window-onerror.https.html") continue;   // all translated above
      const reason = subReason[f.file + "\u0000" + s.name] || fileReason[f.file] || (f.file.startsWith("declarative/") ? "declarative API (form-based tools), which the spec text at 14b6d53 does not define" : null);
      if (!reason) throw new Error("no reason for " + key + " " + name);
      out.push({ file, subtest: name, lines: [s.line, s.endLine], scope: "out", reason });
    }
  }
}

// ---- resolve execute ops against the oracle's own getTools() results -------------------------
function runOracle(ops) {
  return JSON.parse(execFileSync(oracle, { input: JSON.stringify(ops) + "\n" }).toString().trim().split("\n")[0]);
}
function resolve(setup, trace) {
  const all = [...setup, ...trace].map((o) => o.op === "execute" ? { ...o, call: typeof o.call === "number" ? o.call : 0, index: 0 } : o);
  const res = runOracle(all.map(({ tool, ...o }) => o));
  let calls = -1; const lists = [];
  const outOps = [...setup, ...trace].map((o, i) => {
    if (o.op === "getTools") { calls++; lists.push(res[i].slice(6).split(";").filter(Boolean).map((t) => t.split("|")[0])); return o; }
    if (o.op !== "execute") return o;
    const call = o.call === "last" ? calls : o.call;
    const index = lists[call].indexOf(o.tool);
    if (index < 0) throw new Error("tool " + o.tool + " not in getTools() call " + call);
    return { op: "execute", call, index, input: o.input };
  });
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
    checks: "`at` indexes the trace (not setup); `want` is what the WPT assertion requires: {outcome} exact oracle outcome string, {names} tool names in order, {count}, or {tool, field} with {equals}|{isNull}|{notNull}|{json}|{path, equals}",
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
