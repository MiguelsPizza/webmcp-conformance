# Results

Model at spec 14b6d53. Polyfill and Chromium 157 ran live (5 seeds × 300 random sequences, shrunk to minimal repros). Every target also ran the recorded corpus `corpus/spec-14b6d53.json` (1,000 sequences, 7,311 calls) with `--replay`.

| Implementation | Result |
|---|---|
| Polyfill main (4c01562) | 1 divergence: stale `Tool` handles |
| Polyfill PR #25 (63ddbfd) | Agrees on every call |
| Chrome 157.0.8103.78 / .80, WebMCP flag on | 4 root causes |
| Chrome Canary 160.0.8177.0, WebMCP flag on | 1 root cause, the open spec question about result serialization |
| Firefox | Not run. Its implementation exposes an earlier, different API (below). |

## Polyfill main

**Stale handle runs the re-registered tool.** Register `c` with a signal, take it from `getTools()`, abort, register a new `c`, then execute the old handle. The spec rejects with `NotFoundError`, but the polyfill runs the new tool. The polyfill looks tools up by name; the spec has looked them up by tool id since #348. *Implementation lagging the spec*, fixed by PR #25.

## Chrome 157 and Canary 160

1. **Result strings aren't JSON-encoded, and `undefined` isn't rejected.** Present in both 157 and Canary 160. A tool resolving with `"hi"` gives `hi` instead of `"hi"`, one resolving with `""` gives `Operation succeeded` instead of `""`, and one resolving with `undefined` gives `undefined` instead of rejecting with `OperationError`. This is deliberate in Chromium (`ToolFunctionFinishedCallback` in `model_context.cc` stringifies primitives). *Open spec question*: spec issue #361 records this exact disagreement and notes WPT follows Chrome.
2. **`UnknownError` instead of `OperationError` / `NotFoundError`.** 157 only. For a rejected tool and for an unregistered tool. The spec switched to specific exceptions in #339. *Version lag*, fixed in Canary 160.
3. **`outputSchema` isn't serialized at registration.** 157 only. An unserializable `outputSchema` registers fine instead of rejecting with `TypeError`. When the signal is also already aborted, that shows up as `AbortError` instead of `TypeError`. *Version lag*, fixed in Canary 160.
4. **Stale handle runs the re-registered tool.** 157 only. The same trace as the polyfill above returns `{"n":5}` instead of `NotFoundError`. *Version lag*, fixed in Canary 160, which looks tools up by tool id.

## Firefox

Firefox has a prototype behind `dom.modelcontext.enabled` ([bug 2018306](https://bugzilla.mozilla.org/show_bug.cgi?id=2018306)). Its WebIDL on `main` (163.0a1) is an earlier API:

- it's on `navigator.modelContext` only
- `registerTool()` is synchronous and takes no options (no `signal`, no `exposedTo`)
- it has `unregisterTool(name)`
- the only discovery and execution calls are test-only `getTools()` and `invokeTool(name, input)` behind `dom.modelcontext.testing.enabled`

So most of the current spec isn't there to compare yet. An adapter could map the shared parts (name validation, duplicates, execution outcomes by name), but tool-id semantics can't be expressed through it.

## Reproducing a single trace

Pipe the trace (a JSON array of operations) into `.lake/build/bin/oracle` to get the spec outcomes.
