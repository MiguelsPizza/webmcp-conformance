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

211 subtests in 85 files. A subtest is **in scope** when it exercises only what the model covers: one same-origin document, `registerTool()` validation, ordering, schemas, annotations and signal unregistration, the members and order of `getTools()`, and `executeTool()` lookup, input, results and errors.

| | Subtests |
|---|---:|
| In scope | 43 |
| &nbsp;&nbsp;agree | 36 |
| &nbsp;&nbsp;disagree | 3 |
| &nbsp;&nbsp;not expressible | 4 |
| Out of scope | 168 |

At the level of single assertions: 121 checks agree and 5 disagree. 28 of those 126 checks use a proxy value (below). 21 assertions inside in-scope subtests can't be expressed. All 5 disagreements are the open spec question [#361](https://github.com/webmachinelearning/webmcp/issues/361). Leaving #361 aside, the model agrees with every WPT assertion it can express.

Per file, for the 17 files with in-scope subtests:

| File | Agree | Disagree | Not expressible | Out of scope |
|---|---:|---:|---:|---:|
| `imperative/duplicate_tool_registration.https.html` | 1 | | | |
| `imperative/executeTool-abort.https.html` | | 1 | | 6 |
| `imperative/executeTool-error-window-onerror.https.html` | 6 | | | |
| `imperative/executeTool-invalid-dictionary.https.html` | 1 | | 1 | |
| `imperative/exposedTo-invalid-origins.https.html` | | 1 | | 11 |
| `imperative/getTools-imperative-annotations.https.html` | 4 | | | |
| `imperative/getTools-imperative-schema.https.html` | 2 | | | |
| `imperative/getTools.https.html` | 1 | | | |
| `imperative/object-arguments.https.html` | | 1 | | |
| `imperative/register-tool-title.https.html` | 2 | | 1 | |
| `imperative/register_tool_invalid_json_schema.https.html` | 8 | | | |
| `imperative/register_tool_name_validation.https.html` | 2 | | | |
| `imperative/register_tool_no_schema.https.html` | 1 | | | |
| `imperative/register_tool_signal.https.html` | 2 | | 2 | |
| `imperative/register_tool_with_empty_annotation.https.html` | 1 | | | |
| `imperative/register_tool_with_schema.https.html` | 4 | | | |
| `imperative/tool-re-registration-race.https.html` | 1 | | | |
| 68 other files | | | | 151 |
| **Total** | **36** | **3** | **4** | **168** |

The 168 out-of-scope subtests, by the first reason that applies: declarative tools 58 (none of which the spec text at `14b6d53` defines), cross-origin frames and `exposedTo`/`fromOrigins` 37, navigation, detached frames and other documents 24, the execution `signal` and cancellation 21, events 16, APIs not in the spec's IDL (`waitForToolsUntil()`, `resumeTool()`) 4, and 8 others (IDL shape and identity, `[SecureContext]`, permissions policy, a `toJSON()` that runs page script, unregistering from inside a running callback). `cases.json` records the reason for each.

## Method

1. **Inventory.** Every `.html`/`.js` test file under `webmcp/` except `resources/` is listed in `cases.json`, with each subtest's name and line range. Subtests generated in loops are listed once per iteration. Crash tests and `idlharness` appear as one row each.
2. **Translation.** For each in-scope subtest, the scenario becomes an oracle trace, and each WPT assertion becomes a check on one outcome. `execute` ops are written by tool name, and `translate.cjs` fills in the index from the oracle's own `getTools()` result for that prefix. A trace's `setup` replays the state that earlier subtests in the same file leave behind, because WPT subtests share one document. For example, `getTools-imperative-schema`'s second subtest still sees `search_tool`.
3. **Awaited calls count.** `await registerTool(...)` fails the subtest if it rejects, so it becomes a check that it fulfils. These are marked `setup: true`. On their own they don't make a subtest count as expressible.
4. **Proxy values.** The model's author-supplied values come from small fixed sets. Where WPT uses a value outside them, the translation substitutes the model value that goes through the same spec steps, and records the substitution in `proxy`. For example, `{toJSON: () => undefined}` becomes a cyclic object (either way, "serializing a JavaScript value to a JSON string" throws a `TypeError`), `BigInt(42)` as a schema becomes the string `"x"` (either way, Web IDL conversion to `object` fails), and a tool returning `'Success'` becomes `returnText`, which returns `'hi'`. The WPT expectation is then restated for that value: "the result is the returned string" becomes `result:hi`.
5. **Not expressible.** Where no model value reaches the same steps, the assertion is listed under `notExpressible` with the reason. Examples: custom abort reasons, primitive or array inputs, lone surrogates, lookalike `Tool` objects, nested schema members. A subtest whose only real assertions are of this kind counts as not expressible.
6. **Scoring.** `tools/wpt-score.cjs` runs every trace through the oracle in one process. A subtest disagrees if any check disagrees. It agrees if every check agrees and at least one isn't a setup check. Otherwise it is not expressible. Every known disagreement carries its classification in `expectDisagree`. The scorer exits non-zero if a disagreement has no classification, or if a classified check starts agreeing, so a change to the model or to `cases.json` can't silently move the score.

## Disagreements

All five come from one cause: **#361, spec vs WPT.** WPT expects `executeTool()` to resolve with the tool's string result unchanged. The spec serializes every fulfilled value to JSON: in "invoke the execute callback", "Let |serializedResult| be the result of serializing a JavaScript value to a JSON string given |v|" ([index.bs L618-L622 at 14b6d53](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L618-L622), [#invoke-the-execute-callback](https://webmachinelearning.github.io/webmcp/#invoke-the-execute-callback)), and `completionSteps` resolves the `Promise<DOMString>` with that string. So a tool returning `'hi'` gives `'"hi"'`. The model follows the spec.

| WPT assertion | Expects | Spec / model |
|---|---|---|
| [`object-arguments.https.html#L58`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L58) `executeTool(tool)` | `Success` | `"Success"` |
| [`object-arguments.https.html#L66`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L66) `executeTool(tool, undefined)` | `Success` | `"Success"` |
| [`object-arguments.https.html#L73`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L73) `executeTool(tool, undefined, {})` | `Success` | `"Success"` |
| [`executeTool-abort.https.html#L28`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-abort.https.html#L28) | `success` | `"success"` |
| [`exposedTo-invalid-origins.https.html#L94`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/exposedTo-invalid-origins.https.html#L94) | `callback2` | `"callback2"` |

These five are the #361 assertions the model can score. The same expectation appears in 18 more: [`object-arguments.https.html#L24`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/object-arguments.https.html#L24), which uses an array input the model can't express, and 17 in out-of-scope subtests (cross-origin, opaque origins, cancellation, iframes). [`issue-361-evidence.md`](issue-361-evidence.md) lists all 23. Object results are the other way round. [`tool-re-registration-race.https.html#L64`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/tool-re-registration-race.https.html#L64) and [`executeTool-unregister-resolution-race.https.html#L36`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/executeTool-unregister-resolution-race.https.html#L36) expect JSON, which agrees with the spec and the model. So WPT encodes Chromium's rule (objects as JSON, primitives as strings, see RESULTS.md), not plain string passthrough.

No disagreement was classified as a model bug, and none as an ambiguity that should make the model allow several outcomes.

## Other findings

These don't change the score, but they came up while reading every file.

1. **Opaque-origin execution: spec vs WPT, not covered by #361.** `executeTool()` step 5 rejects with `NotSupportedError` when the `Tool`'s origin is opaque ([index.bs L1110-L1113](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L1110-L1113)). That step carries `Issue(#349)`: "Allow the execution of tools registered by documents with an opaque origin". [`imperative/opaque-origin-tools.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html) asserts that execution succeeds for opaque-origin tools at [L92](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L92), [L137](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L137), [L200](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L200) and [L237-L238](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/opaque-origin-tools.https.html#L237-L238). [`declarative/opaque-origin-tools.https.html#L36`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/declarative/opaque-origin-tools.https.html#L36) does the same. WPT already implements the resolution #349 proposes. Opaque origins are outside the model, so this isn't in the score. The fix is either to land #349 in the spec or to mark these tests tentative.
2. **WPT tests APIs the spec doesn't define.** All 58 declarative subtests, `waitForToolsUntil()` ([`wait-for-tools-until.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/wait-for-tools-until.https.html), [`detached-frame-waitForToolsUntil.https.html`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/detached-frame-waitForToolsUntil.https.html), [`permissions-policy.https.html#L177-L195`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/permissions-policy.https.html#L177-L195)) and `resumeTool()` ([`permissions-policy.https.html#L159-L176`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/permissions-policy.https.html#L159-L176)) have no counterpart in the spec at `14b6d53`: the `ModelContext` IDL at [L745-L753](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L745-L753) has only `registerTool`, `getTools`, `executeTool` and three event handlers. Two declarative tests also expect `executeTool()` to resolve with `null` ([`executeTool-navigation.https.html#L23`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/declarative/executeTool-navigation.https.html#L23), [`executeTool-respondWith.https.html#L100`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/declarative/executeTool-respondWith.https.html#L100)), but the IDL return type is `Promise<DOMString>` (L748).
3. **A schema whose `toJSON()` returns a primitive: an ambiguity in the spec.** [`register_tool_with_schema.https.html#L37`](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/register_tool_with_schema.https.html#L37) and [L72](https://github.com/web-platform-tests/wpt/blob/e00a7b14e8e3d9c04933e29ed247baf76c60706e/webmcp/imperative/register_tool_with_schema.https.html#L72) register an `inputSchema`/`outputSchema` whose `toJSON()` returns the string `'undefined'`, and expect success. That matches the spec: "serialize a tool schema" ([L687-L691](https://github.com/webmachinelearning/webmcp/blob/14b6d53/index.bs#L687-L691)) doesn't check that the result is an object. But the tool definition's input schema is "a JSON string representing a JSON Schema object" (L222-L225). And `getTools()` would then parse it into the JavaScript string `"undefined"` and expose it through `Tool.inputSchema`, whose IDL type is `object?` (L1439). The spec should either reject non-object serializations with a `TypeError`, as conversion already does for non-object members (note at L232-L237), or say what such a `Tool` exposes. WPT asserts nothing about the resulting `Tool`. The model has no such schema value, so it takes no position.

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
- **Agreement is with what WPT asserts, not with everything a test does.** Assertions the model can't express are listed but not scored. 13 of the 39 scored subtests also contain such assertions.
- **In scope is a small part of the suite.** 43 of 211 subtests. Most of WPT exercises frames, origins, cancellation, events and declarative tools, which the model doesn't cover. A high agreement rate here says nothing about those areas.
- **WPT is not the spec.** Where WPT and the spec disagree, the model follows the spec. Those disagreements are findings about WPT or the spec, not failures of the model.
- **The score is pinned.** It is for WPT `e00a7b1` and spec `14b6d53`. Re-translate changed files when either moves. The scorer's exit status catches drift in the model, but not new or changed WPT files.
