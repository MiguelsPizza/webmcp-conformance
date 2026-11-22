# Results

Model at spec 14b6d53. Every target ran the recorded corpus `corpus/spec-14b6d53.json` (1,000 sequences, 6,316 calls) with `--replay`. The polyfill also ran live with fresh seeds and shrinking. Traces are the shortest or shrunk repros the harness found.

| Implementation | Result |
|---|---|
| Polyfill PR #25 (63ddbfd) | Agrees on every call |
| Chrome Canary 160.0.8177.0, WebMCP flag on | Agrees on every call except the open spec question #361 (154 results); with `--known`, agrees on all 6,316 |
| Polyfill main (4c01562) | 2 divergences, both fixed by PR #25 |
| Chrome 157.0.8103.80, WebMCP flag on | 4 root causes, all fixed in Canary except #361 |
| Firefox | Not run. Its implementation exposes an earlier, different API (below). |

## Polyfill main

1. **`getTools()` returns dictionaries, not `Tool` objects.** Absent `inputSchema`, `outputSchema` and `annotations` come back `undefined` where a `Tool` exposes `null`. *Lagging the spec* (#348), fixed by PR #25.
2. **Stale handle runs the re-registered tool.** Register `c` with a signal, take it from `getTools()`, abort, register a new `c`, then execute the old handle. The spec rejects with `NotFoundError`, but the polyfill runs the new tool, because it looks tools up by name. *Lagging the spec* (#348), fixed by PR #25.

## Chrome Canary 160

**Result strings aren't JSON-encoded, and `undefined` isn't rejected.** A tool resolving with `"hi"` gives `hi` instead of `"hi"`, one resolving with `""` gives `Operation succeeded` instead of `""`, and one resolving with `undefined` gives `undefined` instead of rejecting with `OperationError`. This is deliberate in Chromium (`ToolFunctionFinishedCallback` in `model_context.cc` stringifies primitives). *Open spec question*: spec issue #361 records this exact disagreement and notes WPT follows Chrome.

Everything else in the slice matches, including the new checks: Web IDL conversion failures before the spec steps, the members `getTools()` exposes (title, schemas after `toJSON()`, annotations with defaults), `DataError` for non-object input, and aborting a registration before its promise settles.

## Chrome 157

Besides #361:

1. **`outputSchema` and `annotations` are missing.** `getTools()` exposes neither, and an unserializable or non-object `outputSchema` registers fine instead of throwing `TypeError`. That also shows up as `AbortError` or `InvalidStateError` where the spec's `TypeError` comes first. *Version lag*, fixed in Canary.
2. **`UnknownError` instead of `OperationError` / `NotFoundError`** for a rejected tool and an unregistered tool. The spec switched to specific exceptions in #339. *Version lag*, fixed in Canary.
3. **Stale handle runs the re-registered tool**, as in the polyfill above. *Version lag*, fixed in Canary.

## Firefox

Firefox has a prototype behind `dom.modelcontext.enabled` ([bug 2018306](https://bugzilla.mozilla.org/show_bug.cgi?id=2018306)). Its WebIDL on `main` (163.0a1) is an earlier API:

- it's on `navigator.modelContext` only
- `registerTool()` is synchronous and takes no options (no `signal`, no `exposedTo`)
- it has `unregisterTool(name)`
- the only discovery and execution calls are test-only `getTools()` and `invokeTool(name, input)` behind `dom.modelcontext.testing.enabled`

So most of the current spec isn't there to compare yet. An adapter could map the shared parts (name validation, duplicates, execution outcomes by name), but tool-id semantics can't be expressed through it.

## Reproducing a single trace

Pipe the trace (a JSON array of operations) into `.lake/build/bin/oracle` to get the spec outcomes, or into the harness with `--replay`.
