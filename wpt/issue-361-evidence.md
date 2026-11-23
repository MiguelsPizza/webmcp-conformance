# #361: which WPT assertions expect un-encoded result strings

Draft for the spec's issue #361. Not filed.

---

I scored my Lean model of the spec against the WebMCP web-platform-tests ([wpt `e00a7b1`](https://github.com/web-platform-tests/wpt/tree/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp), spec `14b6d53`). Apart from this issue, every assertion the model can express agrees. Here is exactly where WPT and the spec part ways, so the group can pick a direction.

**The spec.** In "invoke the execute callback", a fulfilled callback's value `v` goes through "serializing a JavaScript value to a JSON string", and `executeTool()` resolves with that string ([index.bs L618-L622](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L618-L622); IDL `Promise<DOMString> executeTool(...)`, [L748](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L748)). A tool returning `'hi'` therefore gives `'"hi"'`, and one returning `undefined` rejects with `OperationError` ("unserializable result").

**WPT.** These 23 assertions expect a tool's string result back unchanged (all paths under `webmcp/imperative/`):

| File | Lines |
|---|---|
| [`object-arguments.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L24) | 24, 58, 66, 73 |
| [`executeTool-abort.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-abort.https.html#L28) | 28, 232 |
| [`exposedTo-invalid-origins.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-invalid-origins.https.html#L94) | 94 |
| [`model_context.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/model_context.https.html#L58) | 58 |
| [`executeTool-events.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-events.https.html#L102) | 102 |
| [`exposedTo-cross-origin-child.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-cross-origin-child.https.html#L62) | 62, 115 |
| [`exposedTo-defaults-same-origin.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-defaults-same-origin.https.html#L54) | 54, 103, 151, 192 |
| [`opaque-origin-tools.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L92) | 92, 137, 200, 237, 238 |
| [`unregister-during-executeTool.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/unregister-during-executeTool.https.html#L96) | 96, 133, 214 |

13 of them run through the model's frame tree and calls in flight, and the model scores them directly (the 13 disagreements in [`README.md`](README.md#disagreements)); the rest use opaque origins, a `createHTMLDocument()` document, an array input or a re-entrant callback, or, at L96 and L133, a string the scoring has to replace with an object result. Line 214 compounds it: the outer tool returns `` `outer:${innerResult}` ``, and the test expects `'outer:inner_done'`.

Object results already match the spec. [`tool-re-registration-race.https.html#L64`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/tool-re-registration-race.https.html#L64) expects `'{"which":"second"}'`, and [`executeTool-unregister-resolution-race.https.html#L36`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-unregister-resolution-race.https.html#L36) expects `'{"status":"resolved"}'`. So WPT follows Chromium's rule (objects as JSON, primitives converted to strings), not plain passthrough. No WPT test covers the values where the two rules differ most: `''`, `undefined`, `null` and numbers.

**Minimal case.**

```js
await document.modelContext.registerTool({name: 'a', description: 'd', execute: () => 'hi'});
const [tool] = await document.modelContext.getTools();
await document.modelContext.executeTool(tool);   // spec: '"hi"'   WPT-style expectation: 'hi'
```

As an oracle trace, with the model's output:

```
$ echo '[{"op":"register","name":"a","title":null,"description":"d","inputSchema":"absent","outputSchema":"absent","annotations":null,"behavior":"returnText","signal":null},{"op":"getTools"},{"op":"execute","call":0,"index":0,"input":"omitted"}]' | .lake/build/bin/oracle
["ok","tools:a||d|null|null|null","result:\"hi\""]
```

Chrome Canary 160 gives `hi` here. It gives `Operation succeeded` for a tool returning `''`, where the spec says `'""'`, and `undefined` for a tool returning `undefined`, where the spec says `OperationError`.

**Options.**

1. **Change the spec to match WPT and Chromium.** Return string results as they are and JSON-serialize everything else. The spec would also need to say what `''`, `undefined`, `null`, numbers and Symbols become, and WPT would need tests for them, because nothing pins those down today. Agents would then not be able to tell a string result from the same text produced as JSON.
2. **Change WPT and Chromium to match the spec.** Keep JSON serialization for every value. The 23 assertions above would expect JSON (for example `'"Success"'`), and Chromium's `ToolFunctionFinishedCallback` would stop converting primitives itself. Every result string would then parse as JSON.

I don't have a strong preference. I'd just like the spec and WPT to agree. Once one is chosen I can update the model and the scoring, and add WPT cases for the untested values.
