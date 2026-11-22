# Results

Model at spec 14b6d53. Each target ran 5 seeds × 300 random sequences (about 2,100 calls per seed). Traces below are the minimal repros the harness shrank them to.

| Implementation | Result |
|---|---|
| Polyfill main (4c01562) | 1 divergence: stale `Tool` handles |
| Polyfill PR #25 (63ddbfd) | Agrees on every call |
| Chromium 157.0.8103.78, `--enable-blink-features=WebMCP` | 4 root causes; 3 look fixed on Chromium main, 1 is an open spec question |
| Firefox | Not run. Its implementation exposes an earlier, different API (below). |

## Polyfill main

**Stale handle runs the re-registered tool.** Register `c` with a signal, take it from `getTools()`, abort, register a new `c`, then execute the old handle. The spec rejects with `NotFoundError`, but the polyfill runs the new tool. The polyfill looks tools up by name; the spec has looked them up by tool id since #348. *Implementation lagging the spec*, fixed by PR #25.

## Chromium 157

1. **Result strings aren't JSON-encoded, and `undefined` isn't rejected.** A tool resolving with `"hi"` gives `hi` instead of `"hi"`, and one resolving with `undefined` gives `"undefined"` instead of rejecting with `OperationError`. Chromium main still stringifies primitives this way (`ToolFunctionFinishedCallback` in `model_context.cc`). *Open spec question*: spec issue #361 records this exact disagreement and notes WPT follows Chrome.
2. **`UnknownError` instead of `OperationError` / `NotFoundError`.** For a rejected tool and for an unregistered tool. The spec switched to specific exceptions in #339, and Chromium main has the new names. *Version lag.*
3. **`outputSchema` isn't serialized at registration.** An unserializable `outputSchema` registers fine instead of rejecting with `TypeError`. When the signal is also already aborted, that shows up as `AbortError` instead of `TypeError`. Chromium main serializes it. *Version lag.*
4. **Stale handle runs the re-registered tool.** The same trace as the polyfill above returns `{"n":5}` instead of `NotFoundError`. Chromium main keys tools by tool id. *Version lag.*

The "fixed on main" calls come from reading Chromium's source at version 160.0.8179.0. They haven't been run, because no newer Chromium build was reachable from where this ran. `node harness/run.cjs chromium:<path to Canary>` would confirm them.

## Firefox

Firefox has a prototype behind `dom.modelcontext.enabled` ([bug 2018306](https://bugzilla.mozilla.org/show_bug.cgi?id=2018306)). Its WebIDL on `main` (163.0a1) is an earlier API:

- it's on `navigator.modelContext` only
- `registerTool()` is synchronous and takes no options (no `signal`, no `exposedTo`)
- it has `unregisterTool(name)`
- the only discovery and execution calls are test-only `getTools()` and `invokeTool(name, input)` behind `dom.modelcontext.testing.enabled`

So most of the current spec isn't there to compare yet. An adapter could map the shared parts (name validation, duplicates, execution outcomes by name), but tool-id semantics can't be expressed through it.

## Reproducing a single trace

Pipe the trace (a JSON array of operations) into `.lake/build/bin/oracle` to get the spec outcomes.
