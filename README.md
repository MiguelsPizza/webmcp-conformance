# WebMCP conformance: a Lean reference model

An executable model of the [WebMCP spec](https://webmachinelearning.github.io/webmcp/) in Lean 4, with machine-checked proofs about it, and a harness that runs the same random API-call sequences against implementations (today the polyfill and Chromium builds), compares each call with the model, and shrinks every disagreement to a minimal repro.
The aim is one concrete target for implementers instead of each reading the prose differently. The approach follows [Cedar](https://github.com/cedar-policy/cedar-spec): a small, readable model that is both executable and the subject of proofs, used as the oracle for differential random testing.

## Findings at a glance

Each implementation replayed the recorded corpus of 1,000 sequences (6,146 calls). Details, repros and the full table are in [RESULTS.md](RESULTS.md).

| Implementation | Against the model |
|---|---|
| Polyfill [PR #25](https://github.com/w3c-oss/webmcp-polyfill/pull/25) (63ddbfd) | Agrees on 6,123 calls. The other 23 are two bugs: permissions policy checked after the arguments, and duplicate names found late within one script |
| Polyfill main (4c01562) | Those two, plus two that PR #25 fixes (dictionaries instead of `Tool` objects, and a stale `Tool` running a re-registered tool) and an aborted execution not running its callback, which may be a spec issue |
| Chrome Canary 160.0.8177.0 (hand run) | Agrees on every call except the open spec question [#361](https://github.com/webmachinelearning/webmcp/issues/361): result strings aren't JSON-encoded |
| Chromium 157.0.8103.78 (Playwright's) | #361 plus 5 root causes of version lag, all fixed in Canary, and an intermittent hang in one frame |
| Chrome 157.0.8103.80 (hand run) | #361 plus 4 of those 5 root causes |

Against the official web-platform-tests, 89 of 211 subtests can be translated into the model, and it agrees with every assertion it can express except the 13 that turn on #361 ([wpt/README.md](wpt/README.md)).

## What is claimed and what isn't

- **Proofs** are about the model. They show the spec's algorithms, as transcribed here, keep the properties below; they say nothing directly about any implementation.
- **Testing** is the link to implementations. A pass means an implementation matched the model on every generated sequence, not that it is correct. The model transcribes spec prose, so each disagreement needs a person to decide whether the implementation, the spec or the model is wrong; when every implementation disagrees the same way, suspect the model or the spec first.
- **WPT scoring** compares the model with what WPT asserts, through a hand translation recorded subtest by subtest. Where WPT and the spec disagree, the model follows the spec.

## Scope

A fixed frame tree of five documents on three origins (`harnessDocs` in [`WebMCP/Model.lean`](WebMCP/Model.lean)), one of them a cross-origin `<iframe>` that doesn't delegate "tools". The model covers `registerTool()` (Web IDL conversion, validation in spec order, schemas, `exposedTo`, unregistration through the signal, permissions policy), `getTools()` (`fromOrigins`, which documents and tools the caller sees, the members of each `Tool`, order), `executeTool()` (lookup in the `Tool`'s source document, the exposure check, input, results and errors), and calls started from one script before any is awaited (`Op.concurrent`), including aborting an execution's `signal`, with every outcome the spec's ordering allows. Author-supplied values come from small fixed sets.

Not modelled yet: events, the callback's own `signal`, calls from several documents' scripts at once, callbacks that do more than settle or unregister their own tool, navigation and unloading, documents in other traversables, opaque origins, and other frame trees. The header of `Model.lean` lists every simplification.

## What's proved

[`WebMCP/Proofs.lean`](WebMCP/Proofs.lean) proves an invariant for every state reachable by any sequence of calls, in every branch the spec allows for calls in flight (`reachable_invariant`, `concurrent_spec`): names are unique per document, a tool id identifies one registration, every registered tool is valid and lives in a document allowed to use "tools", and every `Tool` object's name, `source` and `origin` match the registration its tool id points to. Every operation but `Op.concurrent` has exactly one outcome (`step_deterministic`). From the invariant:

- **A tool is only discovered by an origin it is exposed to** (`getTools_exposed`): every `Tool` `getTools()` returns comes from a document allowed to use "tools" that is same origin with the caller or in its `fromOrigins`, and is exposed to the caller's origin (`getTools_same_origin`, `getTools_not_from_disallowed`).
- **A tool never runs for an origin it is not exposed to.** An awaited `executeTool()` on it rejects with `NotAllowedError`, `TypeError` or `NotFoundError` before the callback runs (`executeTool_not_exposed`). Started in an `Op.concurrent` alongside any other calls, it rejects with one of those or `AbortError` in every order, and its queued tool execute steps leave the page unchanged (`concurrent_not_exposed`, `asyncStep_not_exposed`).
- **The spec's `executeTool()` assertions hold** (`execute_assert_name`): in a document allowed to use "tools", once the input is serialized, the call rejects with `NotFoundError` or runs exactly the registration the `Tool` names, in the document of its `origin`.
- **The spec's "unregister a tool" assertion holds** (`unregister_assert_exists`), and so does `registerTool()`'s `Assert: signal is not aborted` (`registerTool_assert_signal`).
- **A `Tool` whose registration is gone never runs anything again** (`stale_tool_not_found`): it fails with `NotFoundError` (or earlier `TypeError`/`NotAllowedError`) whenever it is executed, even if a new tool takes its name.
- **Unregistration racing execution** (`unregistration_execution_race`): for the script `executeTool(tool, input)` with no `signal`, then aborting the signal `tool`'s registration was made with, then `registerTool(t)` with no `signal` or `exposedTo` (any name, such as the old one), in one document, every order rejects the execution with `NotFoundError` (or an earlier `NotAllowedError` or `TypeError`), settles the abort, and settles the registration as it would right after the unregistration.
- **Aborting an execution** (`cancel_rejects`): for the script `executeTool(tool, input, {signal})` then `controller.abort()`, in a document allowed to use "tools" and with an input that serializes, every order rejects the call with `AbortError` and settles the abort.
- **A tool that unregisters itself still completes** (`unregisterSelf_completes`), and is gone afterwards.
- `getTools()` is sorted by name (`getTools_sorted`, `getTools_names_unique`); a fulfilled `registerTool()` shows up in the next `getTools()` with what was passed in (`registerTool_then_getTools`); aborting a signal removes exactly its tools (`unregisterBySignal_tools`); a rejected `registerTool()` changes nothing (`registerTool_err_state`).

## Running it

Replay the corpus against an implementation, without Lean:

```
npm install && npx playwright install chromium
node harness/run.cjs chromium --replay corpus/spec-14b6d53.json   # or polyfill:<path to dist/polyfill.js>
```

With Lean 4.36.0 (pinned in `lean-toolchain`):

```
lake test                              # the corpus and repros still match the model; no browser
bash .github/spec-update/check.sh      # everything the Check workflow runs
```

## Layout

| Path | What it is |
|---|---|
| [`WebMCP/Model.lean`](WebMCP/Model.lean) | The model; each definition cites the spec algorithm it transcribes |
| [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean), [`WebMCP/Examples.lean`](WebMCP/Examples.lean) | The proofs (the build fails on `sorry`), and hand-written traces with the outcomes the spec requires |
| [`WebMCP/Oracle.lean`](WebMCP/Oracle.lean), [`Main.lean`](Main.lean), [`ReplayTest.lean`](ReplayTest.lean) | The oracle (JSON traces in, the spec's outcomes out) and `lake test` |
| [`harness/`](harness/run.cjs), [`corpus/`](corpus/README.md), [`expectations/`](expectations/README.md), [`results/`](results/README.md) | The harness, the recorded traces, known divergences per target, and machine-written results |
| [`repros/`](repros), [`wpt-export/`](wpt-export/README.md) | One minimal trace per finding, and the same as WPT tests |
| [`wpt/`](wpt/README.md) | The model scored against web-platform-tests |
| [`spec/anchors.json`](spec/anchors.json), [`tools/`](tools) | The spec commit modelled and a hash of each passage, and the scripts that check them |

More detail:

- [docs/reading-lean.md](docs/reading-lean.md): reading `Model.lean` without knowing Lean
- [docs/spec-mapping.md](docs/spec-mapping.md): each spec anchor's definitions, theorems and examples
- [docs/harness.md](docs/harness.md): targets, generating and shrinking traces, how outcomes are compared, expectations, the WPT export
- [docs/maintaining.md](docs/maintaining.md): building the HTML docs, and keeping the model current with the spec
