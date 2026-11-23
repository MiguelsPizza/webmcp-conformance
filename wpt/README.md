# Scoring the model against web-platform-tests

The official conformance suite for WebMCP is [`webmcp/`](https://github.com/web-platform-tests/wpt/tree/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp) in web-platform-tests (WPT). This directory scores the Lean model against it, the way [EvmYul](https://github.com/NethermindEth/EVMYulLean) scores its EVM model against `ethereum/tests`: each WPT subtest the model can speak to is translated into an oracle trace, and the model's outcome is compared with what the WPT assertion expects.

- WPT: [`e00a7b14e8e3d9c04933e29ed247baf76c60706e`](https://github.com/web-platform-tests/wpt/tree/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp) (2026-11-22), sparse checkout of `webmcp/`
- Spec: webmachinelearning/webmcp at `14b6d53`, the commit the model reflects (`spec/anchors.json`)
- Translation: [`cases.json`](cases.json), written out by [`translate.cjs`](translate.cjs), which holds the hand translation as code. Scorer: [`tools/wpt-score.cjs`](../tools/wpt-score.cjs)

```
lake build WebMCP oracle
node tools/wpt-score.cjs            # --verbose prints every check
```

## Score

211 subtests in 85 files. A subtest is **in scope** when every call it makes is one the model covers, and at least one of its assertions is about a call's outcome. The model covers `registerTool()` (validation in spec order, schemas, annotations, `exposedTo` and its `SecurityError`, signal unregistration), `getTools()` (`fromOrigins`, which documents' tools are discovered and which are exposed to the caller, their members and order), and `executeTool()` (lookup in the `Tool`'s source document, the exposure check, input, results and errors), for a frame tree of five documents on three origins with the "tools" permissions policy, and calls started together without awaiting, including aborting an execution's `signal`. Assertions about events or a callback's own `options.signal` are listed as not expressible.

| | Subtests |
|---|---:|
| In scope | 89 |
| &nbsp;&nbsp;agree | 76 |
| &nbsp;&nbsp;disagree | 11 |
| &nbsp;&nbsp;not expressible | 2 |
| Out of scope | 122 |

At the level of single assertions: 233 checks agree and 13 disagree. 72 of those 246 checks use a proxy value (below). 45 assertions inside in-scope subtests can't be expressed. All 13 disagreements are the open spec question [#361](https://github.com/webmachinelearning/webmcp/issues/361). Leaving #361 aside, the model agrees with every WPT assertion it can express, including every cross-origin, `exposedTo`, `fromOrigins`, permissions-policy and cancellation assertion.

Per file, for the 29 files with in-scope subtests:

| File | Agree | Disagree | Not expressible | Out of scope |
|---|---:|---:|---:|---:|
| `imperative/duplicate_tool_registration.https.html` | 1 | | | |
| `imperative/executeTool-abort.https.html` | 3 | 2 | | 2 |
| `imperative/executeTool-error-window-onerror.https.html` | 6 | | | |
| `imperative/executeTool-events.https.html` | 2 | 1 | | |
| `imperative/executeTool-invalid-dictionary.https.html` | 1 | | 1 | |
| `imperative/executeTool-signal-cross-origin.https.html` | 2 | | | 1 |
| `imperative/executeTool-unregister-resolution-race.https.html` | 1 | | | |
| `imperative/exposedTo-cross-origin-child.https.html` | 2 | 2 | | 1 |
| `imperative/exposedTo-defaults-cross-origin.https.html` | 4 | | | |
| `imperative/exposedTo-defaults-same-origin.https.html` | | 4 | | |
| `imperative/exposedTo-invalid-origins.https.html` | 11 | 1 | | |
| `imperative/exposedTo-multiple-children.https.html` | 1 | | | |
| `imperative/getTools-filtering.https.html` | 2 | | | |
| `imperative/getTools-imperative-annotations.https.html` | 4 | | | |
| `imperative/getTools-imperative-schema.https.html` | 2 | | | |
| `imperative/getTools.https.html` | 1 | | | |
| `imperative/object-arguments.https.html` | | 1 | | |
| `imperative/permissions-policy.https.html` | 5 | | | 3 |
| `imperative/register-tool-title.https.html` | 2 | | 1 | |
| `imperative/register_tool_invalid_json_schema.https.html` | 8 | | | |
| `imperative/register_tool_name_validation.https.html` | 2 | | | |
| `imperative/register_tool_no_schema.https.html` | 1 | | | |
| `imperative/register_tool_signal.https.html` | 4 | | | |
| `imperative/register_tool_with_empty_annotation.https.html` | 1 | | | |
| `imperative/register_tool_with_schema.https.html` | 4 | | | |
| `imperative/same-origin-iframe-registerTool-regression.https.html` | 1 | | | |
| `imperative/tool-re-registration-race.https.html` | 1 | | | |
| `imperative/unregister-during-executeTool.https.html` | 3 | | | 1 |
| `tool-cancel-event.https.html` | 1 | | | 3 |
| 56 other files | | | | 111 |
| **Total** | **76** | **11** | **2** | **122** |

The 122 out-of-scope subtests, by the first reason that applies: declarative tools 58 (none of which the spec text at `14b6d53` defines), navigation, detached frames, crash tests and documents in other frame trees 34, events alone 9, APIs not in the spec's IDL (`waitForToolsUntil()`, `resumeTool()`) 7, opaque origins 5, callbacks that do more than settle or unregister their own tool (abort their caller's signal, call `executeTool()` themselves), or assertions only on a callback's own `options.signal` 4, and 5 others (IDL shape and identity, `[SecureContext]`, a `toJSON()` that runs page script). `cases.json` records the reason for each.

## Method

1. **Inventory.** Every `.html`/`.js` test file under `webmcp/` except `resources/` is listed in `cases.json`, with each subtest's name and line range. Subtests generated in loops are listed once per iteration. Crash tests and `idlharness` appear as one row each.
2. **Translation.** For each in-scope subtest, the scenario becomes an oracle trace, and each WPT assertion becomes a check on one outcome (or on one action's outcome of a `concurrent` operation). `execute` ops are written by tool name, and `translate.cjs` fills in the index from the oracle's own `getTools()` results for the ops before it. A trace's `setup` replays the state that earlier subtests in the same file leave behind, because WPT subtests share one document. For example, `getTools-imperative-schema`'s second subtest still sees `search_tool`. Each subtest removes its iframes in cleanup, which takes their tools with them, so `setup` only ever replays the test page's own tools.
3. **Frames and origins.** WPT's documents map onto the model's frame tree (`harnessDocs` in `WebMCP/Model.lean`): the test page is document 0 (origin 0), a same-origin `<iframe>` is document 1, an `HTTPS_REMOTE_ORIGIN` `<iframe>` with `allow="tools ..."` is document 3 (origin 1) and one without it document 4, and an `HTTPS_OTHER_NOTSAMESITE_ORIGIN` frame is document 2 (origin 2), or origin 3 (no document) when the test has no document of it. A message the test posts to an iframe becomes the op that iframe's handler runs (`resources/iframe-register-tool.html`), in that document. Two placements differ from WPT and are recorded as proxies: the model's document 2 is nested in document 1, where WPT's third-origin frames are children of the test page (`getTools()` walks the whole tree, so this doesn't change what any call sees), and the model has no same-origin document that is denied "tools", so a same-origin `<iframe allow="tools 'none'">` becomes document 4 (the check that rejects looks only at whether the document is allowed).
4. **Calls in flight.** A call followed in the same script by `controller.abort()` becomes a `concurrent` operation with an `execute` action and a `cancel` of it. Where WPT aborts later, after awaiting the callback's start, the trace still cancels in the same script, and records that as a proxy: the abort steps reject the promise whenever they run ([index.bs L1146-L1148](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L1146-L1148)), and cancelling doesn't stop a callback that has started, so the outcome is the same. A tool that is unregistered while its callback is pending (by the test, the iframe, or itself) becomes an `unregisterSelf` tool, whose callback aborts its own registration signal and then resolves with its input: in both, the unregistration comes after "invoke the execute callback" has started.
5. **Awaited calls count.** `await registerTool(...)` fails the subtest if it rejects, so it becomes a check that it fulfils. These are marked `setup: true`. On their own they don't make a subtest count as expressible.
6. **Proxy values.** The model's author-supplied values come from small fixed sets. Where WPT uses a value outside them, the translation substitutes the model value that goes through the same spec steps, and records the substitution in `proxy`. For example, `{toJSON: () => undefined}` becomes a cyclic object (either way, "serializing a JavaScript value to a JSON string" throws a `TypeError`), `BigInt(42)` as a schema becomes the string `"x"` (either way, Web IDL conversion to `object` fails), `'ftp://example.com'` in `exposedTo` becomes a URL whose origin isn't potentially trustworthy, a tool that never settles becomes one that resolves when the call is cancelled anyway, and a tool returning `'Success'` becomes `returnText`, which returns `'hi'`. The WPT expectation is then restated for that value: "the result is the returned string" becomes `result:hi`. A custom abort reason (`controller.abort('cancel 1')`, `AbortSignal.abort('aborted')`) becomes the default one, so "rejects with exactly the abort reason" becomes `err:AbortError`; the model's signals only have the default reason. For two `register_tool_signal` subtests that makes the trace the same as a neighbouring subtest's, which the `proxy` says.
7. **Not expressible.** Where no model value reaches the same steps, the assertion is listed under `notExpressible` with the reason. Examples: events, a callback's own `options.signal`, primitive or array inputs, lone surrogates in titles, lookalike `Tool` objects, nested schema members. A subtest whose only real assertions are of this kind counts as not expressible.
8. **Scoring.** `tools/wpt-score.cjs` runs every trace through the oracle in one process. Where the model allows several outcomes for an op, a check agrees only if every one of them satisfies it (no check in the current translation has more than one). A subtest disagrees if any check disagrees. It agrees if every check agrees and at least one isn't a setup check. Otherwise it is not expressible. Every known disagreement carries its classification in `expectDisagree`. The scorer exits non-zero if a disagreement has no classification, or if a classified check starts agreeing, so a change to the model or to `cases.json` can't silently move the score.

## Disagreements

All thirteen come from one cause: **#361, spec vs WPT.** WPT expects `executeTool()` to resolve with the tool's string result unchanged. The spec serializes every fulfilled value to JSON: in "invoke the execute callback", "Let |serializedResult| be the result of serializing a JavaScript value to a JSON string given |v|" ([index.bs L618-L622 at 14b6d53](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L618-L622), [#invoke-the-execute-callback](https://webmachinelearning.github.io/webmcp/#invoke-the-execute-callback)), and `completionSteps` resolves the `Promise<DOMString>` with that string. So a tool returning `'hi'` gives `'"hi"'`. The model follows the spec.

| WPT assertion | Expects | Spec / model |
|---|---|---|
| [`object-arguments.https.html#L58`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L58) `executeTool(tool)` | `Success` | `"Success"` |
| [`object-arguments.https.html#L66`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L66) `executeTool(tool, undefined)` | `Success` | `"Success"` |
| [`object-arguments.https.html#L73`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L73) `executeTool(tool, undefined, {})` | `Success` | `"Success"` |
| [`executeTool-abort.https.html#L28`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-abort.https.html#L28)  | `success` | `"success"` |
| [`executeTool-abort.https.html#L232`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-abort.https.html#L232) second of two concurrent executions | `exec2 result` | `"exec2 result"` |
| [`exposedTo-invalid-origins.https.html#L94`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-invalid-origins.https.html#L94)  | `callback2` | `"callback2"` |
| [`executeTool-events.https.html#L102`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-events.https.html#L102) tool in a same-origin iframe | `iframe result` | `"iframe result"` |
| [`exposedTo-cross-origin-child.https.html#L62`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-cross-origin-child.https.html#L62) cross-origin iframe runs the parent's tool | `hello` | `"hello"` |
| [`exposedTo-cross-origin-child.https.html#L115`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-cross-origin-child.https.html#L115) parent runs a cross-origin iframe's tool | `hello from iframe` | `"hello from iframe"` |
| [`exposedTo-defaults-same-origin.https.html#L54`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-defaults-same-origin.https.html#L54) same-origin iframe runs the parent's tool | `hello` | `"hello"` |
| [`exposedTo-defaults-same-origin.https.html#L103`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-defaults-same-origin.https.html#L103) same-origin iframe runs the parent's tool | `hello` | `"hello"` |
| [`exposedTo-defaults-same-origin.https.html#L151`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-defaults-same-origin.https.html#L151) parent runs a same-origin iframe's tool | `hello from iframe` | `"hello from iframe"` |
| [`exposedTo-defaults-same-origin.https.html#L192`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-defaults-same-origin.https.html#L192) parent runs a same-origin iframe's tool | `hello from iframe` | `"hello from iframe"` |

These thirteen are the #361 assertions the model can score. The same expectation appears in 10 more: [`object-arguments.https.html#L24`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L24), which uses an array input the model can't express; [`unregister-during-executeTool.https.html#L96`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/unregister-during-executeTool.https.html#L96) and [L133](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/unregister-during-executeTool.https.html#L133), which are scored, but through `unregisterSelf`, whose result is an object, so their #361 half isn't tested; and 7 in out-of-scope subtests (opaque origins, `createHTMLDocument()`, a re-entrant callback). [`issue-361-evidence.md`](issue-361-evidence.md) lists all 23. Object results are the other way round. [`tool-re-registration-race.https.html#L64`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/tool-re-registration-race.https.html#L64) and [`executeTool-unregister-resolution-race.https.html#L36`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-unregister-resolution-race.https.html#L36) expect JSON, which agrees with the spec and the model. So WPT encodes Chromium's rule (objects as JSON, primitives as strings, see RESULTS.md), not plain string passthrough.

No disagreement was classified as a model bug, and none as an ambiguity that should make the model allow several outcomes. In every concurrent trace the model gives one outcome per action, so no WPT assertion relies on an order the spec leaves open.

## Other findings

These don't change the score, but they came up while reading every file.

1. **Opaque-origin execution: spec vs WPT, not covered by #361.** `executeTool()` step 5 rejects with `NotSupportedError` when the `Tool`'s origin is opaque ([index.bs L1110-L1113](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L1110-L1113)). That step carries `Issue(#349)`: "Allow the execution of tools registered by documents with an opaque origin". [`imperative/opaque-origin-tools.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html) asserts that execution succeeds for opaque-origin tools at [L92](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L92), [L137](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L137), [L200](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L200) and [L237-L238](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L237-L238). [`declarative/opaque-origin-tools.https.html#L36`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/declarative/opaque-origin-tools.https.html#L36) does the same. WPT already implements the resolution #349 proposes. Opaque origins are outside the model, so this isn't in the score. The fix is either to land #349 in the spec or to mark these tests tentative.
2. **WPT tests APIs the spec doesn't define.** All 58 declarative subtests, `waitForToolsUntil()` ([`wait-for-tools-until.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/wait-for-tools-until.https.html), [`detached-frame-waitForToolsUntil.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/detached-frame-waitForToolsUntil.https.html), [`permissions-policy.https.html#L177-L195`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/permissions-policy.https.html#L177-L195)) and `resumeTool()` ([`permissions-policy.https.html#L159-L176`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/permissions-policy.https.html#L159-L176)) have no counterpart in the spec at `14b6d53`: the `ModelContext` IDL at [L745-L753](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L745-L753) has only `registerTool`, `getTools`, `executeTool` and three event handlers. Two declarative tests also expect `executeTool()` to resolve with `null` ([`executeTool-navigation.https.html#L23`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/declarative/executeTool-navigation.https.html#L23), [`executeTool-respondWith.https.html#L100`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/declarative/executeTool-respondWith.https.html#L100)), but the IDL return type is `Promise<DOMString>` (L748).
3. **A schema whose `toJSON()` returns a primitive: an ambiguity in the spec.** [`register_tool_with_schema.https.html#L37`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/register_tool_with_schema.https.html#L37) and [L72](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/register_tool_with_schema.https.html#L72) register an `inputSchema`/`outputSchema` whose `toJSON()` returns the string `'undefined'`, and expect success. That matches the spec: "serialize a tool schema" ([L687-L691](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L687-L691)) doesn't check that the result is an object. But the tool definition's input schema is "a JSON string representing a JSON Schema object" (L222-L225). And `getTools()` would then parse it into the JavaScript string `"undefined"` and expose it through `Tool.inputSchema`, whose IDL type is `object?` (L1439). The spec should either reject non-object serializations with a `TypeError`, as conversion already does for non-object members (note at L232-L237), or say what such a `Tool` exposes. WPT asserts nothing about the resulting `Tool`. The model has no such schema value, so it takes no position.

4. **A cleanup step that unregisters nothing: a WPT slip.** [`exposedTo-cross-origin-child.https.html#L187`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-cross-origin-child.https.html#L187) asks the iframe to unregister `'iframe_tool_to_c'`, but the tool it registered at L172-L179 is `'iframe_tool'`, so the iframe aborts nothing. The assertion after it (L193, the parent still sees no tool) holds either way, so the subtest passes without testing what its comment says. The trace has no abort, and agrees.

## Spec steps no WPT test covers

These steps are in the model's slice, but nothing under `webmcp/` at this WPT commit exercises them. Each line gives the model's outcome, which is what a new WPT test would assert. All of them can be written as single-document `promise_test`s.

| Step (index.bs at 14b6d53) | Scenario | Spec / model outcome |
|---|---|---|
| `registerTool()` L839: empty description | `description: ''` | `InvalidStateError` |
| Web IDL: required `description` | `description` omitted | `TypeError` |
| Order: description before schema (L839-L840 before L842) | `description: ''` and a cyclic `inputSchema` | `InvalidStateError` |
| Order: name before schema (L834-L837 before L842) | name `'a b'` and a cyclic `inputSchema` | `InvalidStateError` |
| Order: dictionary conversion before every step | name `'a b'` and `inputSchema: 'x'` | `TypeError` |
| Order: duplicate, name and description before the signal (L829-L840 before L866) | a duplicate name, an invalid name, or an empty description, each with an already-aborted signal | `InvalidStateError` (WPT only tests the schema checks before the signal) |
| Abort steps for each registration (L895-L901) | two tools registered with one signal, then abort | both are gone from `getTools()` |
| `getTools()` sort: "code unit less than" (L1086-L1087) | names `a`, `_`, `B`, `0`, `.`, `-` | `- . 0 B _ a` (WPT only sorts lower-case letters) |
| `getTools()` exposes the serialized schema (L1050-L1053) | `inputSchema` whose `toJSON()` returns `{type:'string'}` | `tool.inputSchema` is `{type:'string'}` |
| `executeTool()` serializes input before the lookup (L1120, then the in-parallel steps) | an unregistered `Tool` with a cyclic input | `TypeError`, not `NotFoundError` |
| "invoke the execute callback" L576-L582: invalid input | input whose `toJSON()` returns `5` | `DataError` |
| The callback gets a JSON copy (L576) | input `{n: 1, f() {}}` | the tool sees only `n` |
| Tool rejected: synchronous throw (L624-L636; Web IDL turns it into a rejection) | `execute() { throw ... }`, not `async` | `OperationError` (WPT only throws from an `async` function) |
| "tool not found", plain unregistration | abort, then execute the old `Tool`, with no re-registration | `NotFoundError` |
| Result serialization of other values (L618-L622) | the tool returns `''`, `null`, `5`, `undefined` | `'""'`, `'null'`, `'5'`, `OperationError`. Blocked on #361: Chromium gives `Operation succeeded` for `''` and `undefined` for `undefined`. |

The traces for each are in the model's value sets (`Schema`, `Input`, `Behavior` in `WebMCP/Model.lean`), and the outcomes above come from the oracle.

## What the score means, and what it doesn't

- **The translation is by hand.** Each trace is one reader's rendering of a JavaScript test into the model's vocabulary. A wrong trace or a wrong expectation would show up as a false agreement or a false disagreement. A second reader should check `cases.json` against the WPT files, especially the `proxy` entries, which are judgement calls about which spec steps a substituted value reaches.
- **Agreement is with what WPT asserts, not with everything a test does.** Assertions the model can't express are listed but not scored. 35 of the 87 scored subtests also contain such assertions, mostly about events and a callback's own `options.signal`.
- **In scope is under half the suite.** 89 of 211 subtests. The rest exercise declarative tools, navigation and detached frames, events, opaque origins and APIs the spec doesn't define, which the model doesn't cover. A high agreement rate here says nothing about those areas.
- **The frame tree is fixed.** WPT builds its own frames per test; the traces place them in the model's five documents (Method, step 3). A test that needs a frame tree of another shape, or two documents of one origin that differ in permissions policy, is translated through a proxy or not at all.
- **WPT is not the spec.** Where WPT and the spec disagree, the model follows the spec. Those disagreements are findings about WPT or the spec, not failures of the model.
- **The score is pinned.** It is for WPT `e00a7b1` and spec `14b6d53`. Re-translate changed files when either moves. The scorer's exit status catches drift in the model, but not new or changed WPT files.
