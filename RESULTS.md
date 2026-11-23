# Results

Model at spec 14b6d53. Every target ran the recorded corpus `corpus/spec-14b6d53.json` (1,000 sequences, 6,316 calls) with `--replay`. The polyfill also ran live with fresh seeds and shrinking. Traces are the shortest or shrunk repros the harness found.

Each row comes from, with Playwright 1.63.0:

```
node harness/run.cjs <target> --replay corpus/spec-14b6d53.json [--known]
```

where `<target>` is `polyfill:<checkout>/dist/polyfill.js` for the polyfill rows and `chromium:<path to the Chrome binary>` for the Chrome rows.

| Implementation | Result |
|---|---|
| Polyfill [PR #25](https://github.com/w3c-oss/webmcp-polyfill/pull/25) (63ddbfd) | Agrees on every call |
| Chrome Canary 160.0.8177.0, WebMCP flag on | Agrees on every call except the open spec question [#361](https://github.com/webmachinelearning/webmcp/issues/361) (154 `executeTool()` result strings); with `--known`, agrees on all 6,316 |
| Polyfill main (4c01562) | 2 divergences, both fixed by PR #25 |
| Chrome 157.0.8103.80, WebMCP flag on | #361 plus 3 other root causes, all 3 fixed in Canary |
| Firefox | Not run. Its implementation exposes an earlier, different API (below). |

## Polyfill main

1. **`getTools()` returns dictionaries, not `Tool` objects.** Absent `inputSchema`, `outputSchema` and `annotations` come back `undefined` where a `Tool` exposes `null`. *Lagging the spec* ([#348](https://github.com/webmachinelearning/webmcp/pull/348)), fixed by PR #25.
2. **Stale handle runs the re-registered tool.** Register `c` with a signal, take it from `getTools()`, abort, register a new `c`, then execute the old handle. The spec rejects with `NotFoundError`, but the polyfill runs the new tool, because it looks tools up by name. *Lagging the spec* (#348), fixed by PR #25.

## Chrome Canary 160

**Result strings aren't JSON-encoded, and `undefined` isn't rejected.** A tool resolving with `"hi"` gives `hi` instead of `"hi"`, one resolving with `""` gives `Operation succeeded` instead of `""`, and one resolving with `undefined` gives `undefined` instead of rejecting with `OperationError`. This is deliberate in Chromium (`ToolFunctionFinishedCallback` in `third_party/blink/renderer/core/script_tools/model_context.cc` stringifies primitives). *Open spec question*: spec issue #361 records this exact disagreement and notes WPT follows Chrome.

Everything else in the slice matches, including the new checks: Web IDL conversion failures before the spec steps, the members `getTools()` exposes (title, schemas after `toJSON()`, annotations with defaults), `DataError` for non-object input, and aborting a registration before its promise settles.

## Chrome 157

Besides #361:

1. **`outputSchema` and `annotations` are missing.** `getTools()` exposes neither, and an unserializable or non-object `outputSchema` registers fine instead of throwing `TypeError`. That also shows up as `AbortError` or `InvalidStateError` where the spec's `TypeError` comes first. *Version lag*, fixed in Canary.
2. **`UnknownError` instead of `OperationError` / `NotFoundError`** for a rejected tool and an unregistered tool. The spec switched to specific exceptions in [#339](https://github.com/webmachinelearning/webmcp/pull/339). *Version lag*, fixed in Canary.
3. **Stale handle runs the re-registered tool**, as in the polyfill above. *Version lag*, fixed in Canary.

## Firefox

Firefox has a prototype behind `dom.modelcontext.enabled` ([bug 2018306](https://bugzilla.mozilla.org/show_bug.cgi?id=2018306)). Its WebIDL on `main` (163.0a1) is an earlier API:

- it's on `navigator.modelContext` only
- `registerTool()` is synchronous and takes no options (no `signal`, no `exposedTo`)
- it has `unregisterTool(name)`
- the only discovery and execution calls are test-only `getTools()` and `invokeTool(name, input)` behind `dom.modelcontext.testing.enabled`

So most of the current spec isn't there to compare yet. An adapter could map the shared parts (name validation, duplicates, execution outcomes by name), but tool-id semantics can't be expressed through it.

## Reproducing a single trace

Pipe a trace (a JSON array of operations) into the oracle to get the outcomes the spec requires. This one is the simplest stale-handle case: register `a` with signal 0, take it from `getTools()`, abort signal 0, execute the old `Tool`.

```
$ echo '[{"op":"register","name":"a","title":null,"description":"d","inputSchema":"absent","outputSchema":"absent","annotations":null,"behavior":"echo","signal":0},{"op":"getTools"},{"op":"abort","signal":0},{"op":"execute","call":0,"index":0,"input":"obj:1"}]' | .lake/build/bin/oracle
["ok","tools:a||d|null|null|null","ok","err:NotFoundError"]
```

`call` and `index` pick the `Tool` by which `getTools()` call returned it and its position in that list.

## 2026-11-23: frames, origins and calls in flight

The model now covers a five-document frame tree on three origins (`exposedTo`, `fromOrigins`, permissions policy) and calls started together without awaiting (`concurrent`). Run against the re-recorded corpus and the hand-written traces below, with Playwright 1.63.0's Chromium 157.0.8103.78 (WebMCP flag on), polyfill main (4c01562) and polyfill PR #25 (63ddbfd). Cross-origin exposure itself (which frames' tools `getTools()` returns, `SecurityError` for bad origins, `NotAllowedError` without `allow="tools"`) matches in both polyfill builds; in Chromium 157 it is hidden behind the version lag above. New kinds of divergence:

1. **Aborting `executeTool()`'s signal stops the tool's callback** (polyfill main and PR #25). The spec rejects the promise with `AbortError` and cancels in parallel, but nothing stops the queued "tool execute steps", so in every order the spec allows, the callback still runs. Chromium 157 runs it. Here the callback unregisters its own tool, so the last `getTools()` shows whether it ran. *Possibly a spec issue*: the spec may not mean the callback to run.
   ```
   [{"op":"register","name":"a","title":null,"description":"d","inputSchema":"absent","outputSchema":"absent","annotations":null,"behavior":"unregisterSelf","signal":0},{"op":"getTools"},{"op":"concurrent","actions":[{"act":"execute","call":0,"index":0,"input":"obj:1","signal":"live"},{"act":"cancel","target":0}]},{"op":"getTools"}]
   spec:     ["ok","tools:a||d|null|null|null","all:[\"err:AbortError\",\"ok\"]","tools:"]
   polyfill: ["ok","tools:a||d|null|null|null","all:[\"err:AbortError\",\"ok\"]","tools:a||d|null|null|null"]
   ```
2. **Permissions policy is checked after the arguments** (polyfill main and PR #25). In a frame whose `<iframe>` doesn't delegate "tools", `registerTool()` with an invalid name, schema or `exposedTo` rejects with that error, but the spec checks "allowed to use" first and rejects with `NotAllowedError`. Web IDL conversion errors still come first, as both expect.
   ```
   [{"op":"register","name":"b","title":null,"description":"d","inputSchema":"unserializable","outputSchema":"absent","annotations":null,"behavior":"echo","signal":null,"doc":4}]
   spec: ["err:NotAllowedError"]   polyfill: ["err:TypeError"]
   ```
3. **`getTools()` and `registerTool()` sometimes never settle in a same-origin `<iframe>` that embeds a cross-origin frame** (Chromium 157). Out of 100 fresh page loads, `[{"op":"getTools","fromOrigins":[],"doc":1}]` timed out after 5 seconds about 5 times; documents 0, 2 and 3 never did.
4. **`Tool` has no `source`** (Chromium 157, which returns a dictionary with `window` instead, and polyfill main). Tools from other frames therefore print as `@undefined`. *Version lag*; PR #25 has `source`.

Starting `executeTool()` and then unregistering and re-registering its tool in the same script runs the new tool in Chromium 157 and polyfill main, and rejects with `NotFoundError` in PR #25: the stale-handle divergence above, showing up for calls in flight too.
