# Results

Model at spec 14b6d53. Every target ran the recorded corpus `corpus/spec-14b6d53.json` (1,000 sequences, 6,316 calls) with `--replay`. The polyfill and Playwright's Chromium also ran 1,000 fresh traces live (seed 1), with shrinking. Traces are the shortest or shrunk repros the harness found. Each finding below has a minimal repro in [`repros/`](repros).

Rows marked *generated* come from the results files in [`results/`](results), written by the harness on 2026-11-22 with Playwright 1.63.0:

```
node harness/run.cjs <target> --replay corpus/spec-14b6d53.json --results results/<label>.json
```

The harness applies the expected divergences in [`expectations/`](expectations) for the target's family and version: counted under their ids, not failures. Rows marked *hand run* are from earlier runs on real Chrome builds (`chromium:<path to the Chrome binary>`) that weren't available to regenerate.

| Implementation | Result | Source |
|---|---|---|
| Polyfill [PR #25](https://github.com/w3c-oss/webmcp-polyfill/pull/25) (63ddbfd) | Agrees on all 6,316 calls, and on 6,443 live | generated: [replay](results/polyfill-pr25-63ddbfd.json), [live](results/polyfill-pr25-63ddbfd-live.json) |
| Chrome Canary 160.0.8177.0, WebMCP flag on | Agrees on every call except the open spec question [#361](https://github.com/webmachinelearning/webmcp/issues/361) (154 `executeTool()` result strings, all matching the #361 expectations) | hand run |
| Polyfill main (4c01562) | 2 divergences, both fixed by PR #25: 769 `getTools()` results with `undefined` members (expected, `implementation-lag`), and 1 trace with the stale handle | generated: [replay](results/polyfill-main-4c01562.json), [live](results/polyfill-main-4c01562-live.json) |
| Chromium 157.0.8103.78 (Playwright 1.63.0's bundled build), WebMCP flag on | #361 (119 calls) plus 5 other root causes, all fixed in Canary: 5,560 of 6,316 calls compared, 4,395 agree, 952 expected divergences, 213 traces with an unexpected one | generated: [replay](results/chromium-157.0.8103.78.json), [live](results/chromium-157.0.8103.78-live.json) |
| Chrome 157.0.8103.80, WebMCP flag on | #361 plus root causes 1, 2, 3 and 5 below (counted there as 3), all fixed in Canary | hand run |
| Firefox | Not run. Its implementation exposes an earlier, different API (below). | |

The exported WPT tests for these findings, and how each target does on them, are in [`wpt-export/`](wpt-export/README.md).

## Polyfill main

1. **`getTools()` returns dictionaries, not `Tool` objects.** Absent `inputSchema`, `outputSchema` and `annotations` come back `undefined` where a `Tool` exposes `null`. *Lagging the spec* ([#348](https://github.com/webmachinelearning/webmcp/pull/348)), fixed by PR #25. Repro: [`absent-members-null`](repros/absent-members-null.json). Listed in [`expectations/polyfill.json`](expectations/polyfill.json) for versions below 0.2.0, so the run goes on to find the next one.
2. **Stale handle runs the re-registered tool.** Register `a` with a signal, take it from `getTools()`, abort, register a new `a`, then execute the old handle. The spec rejects with `NotFoundError`, but the polyfill runs the new tool, because it looks tools up by name. *Lagging the spec* (#348), fixed by PR #25. Repro: [`stale-handle`](repros/stale-handle.json). It's rare in random traces: 1 corpus trace, and none of the 1,000 live ones.

## Chrome Canary 160

**Result strings aren't JSON-encoded, and `undefined` isn't rejected.** A tool resolving with `"hi"` gives `hi` instead of `"hi"`, one resolving with `""` gives `Operation succeeded` instead of `""`, and one resolving with `undefined` gives `undefined` instead of rejecting with `OperationError`. This is deliberate in Chromium (`ToolFunctionFinishedCallback` in `third_party/blink/renderer/core/script_tools/model_context.cc` stringifies primitives). *Open spec question*: spec issue #361 records this exact disagreement and notes WPT follows Chrome. Three WPT tests assert Chromium's behaviour (listed in [`wpt-export/README.md`](wpt-export/README.md#the-361-tests)). Repros: [`361-string-result`](repros/361-string-result.json), [`361-empty-string-result`](repros/361-empty-string-result.json), [`361-undefined-result`](repros/361-undefined-result.json); expectations: the three `361-*` entries in [`expectations/chromium.json`](expectations/chromium.json).

Everything else in the slice matches, including the new checks: Web IDL conversion failures before the spec steps, the members `getTools()` exposes (title, schemas after `toJSON()`, annotations with defaults), `DataError` for non-object input, and aborting a registration before its promise settles.

## Chromium 157

Measured on Playwright's bundled 157.0.8103.78. The hand run on Chrome 157.0.8103.80 found all but 4. Besides #361:

1. **No `outputSchema`, and `undefined` for absent members.** `getTools()` `Tool`s have no `outputSchema`, and an absent `inputSchema` or `annotations` reads `undefined` instead of `null`. Annotations that were given are exposed, with defaults filled in (the earlier hand-written analysis said annotations were missing altogether; that only holds when none were given). *Version lag*, fixed in Canary. Repros: [`outputschema-annotations-exposed`](repros/outputschema-annotations-exposed.json), [`absent-members-null`](repros/absent-members-null.json). Expected as `chromium-157-tool-members` (684 calls).
2. **`outputSchema` isn't validated.** An unserializable or non-object `outputSchema` registers fine instead of throwing `TypeError`. That also shows up as `AbortError` or `InvalidStateError` where the spec's `TypeError` comes first. *Version lag*, fixed in Canary. Repro: [`outputschema-validated`](repros/outputschema-validated.json). Not an expectation, because it leaves an extra tool registered: 191 of the 213 unexpected traces.
3. **`UnknownError` instead of `OperationError` / `NotFoundError`** for a rejected tool and an unregistered tool. The spec switched to specific exceptions in [#339](https://github.com/webmachinelearning/webmcp/pull/339). *Version lag*, fixed in Canary. Repros: [`unknownerror-rejected-callback`](repros/unknownerror-rejected-callback.json), [`unknownerror-unregistered-tool`](repros/unknownerror-unregistered-tool.json). Expected as `chromium-157-unknownerror-*` (123 and 26 calls).
4. **`UnknownError` instead of `DataError`** for input whose JSON serialization isn't an object. The hand run missed this one; the generated run finds it in 21 corpus traces. *Version lag*, fixed in Canary (which gives `DataError`, above). Repro: [`dataerror-non-object-input`](repros/dataerror-non-object-input.json).
5. **Stale handle runs the re-registered tool**, as in the polyfill above. *Version lag*, fixed in Canary. Repro: [`stale-handle`](repros/stale-handle.json).

The 1 and 3 expectations are scoped to versions below 160, so they don't hide a regression in a current build.

## Firefox

Firefox has a prototype behind `dom.modelcontext.enabled` ([bug 2018306](https://bugzilla.mozilla.org/show_bug.cgi?id=2018306)). Its WebIDL on `main` (163.0a1) is an earlier API:

- it's on `navigator.modelContext` only
- `registerTool()` is synchronous and takes no options (no `signal`, no `exposedTo`)
- it has `unregisterTool(name)`
- the only discovery and execution calls are test-only `getTools()` and `invokeTool(name, input)` behind `dom.modelcontext.testing.enabled`

So most of the current spec isn't there to compare yet. An adapter could map the shared parts (name validation, duplicates, execution outcomes by name), but tool-id semantics can't be expressed through it.

## Reproducing a finding

Each file in [`repros/`](repros) is one minimal trace in the corpus format, with a `comment` giving what it shows, the spec anchors, the model's outcomes and each implementation's. Run one against an implementation, or get the model's outcomes from the oracle:

```
$ node harness/run.cjs <target> --replay repros/stale-handle.json
$ node -e 'console.log(JSON.stringify(require("./repros/stale-handle.json").traces[0].ops))' | .lake/build/bin/oracle
["ok","tools:a||d|null|null|null","ok","ok","err:NotFoundError"]
```

`lake test` checks that every repro's recorded outcomes are still the model's. In a trace, `call` and `index` pick the `Tool` by which `getTools()` call returned it and its position in that list.
