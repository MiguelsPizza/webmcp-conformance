# WebMCP conformance: a Lean reference model

[![Check](https://github.com/MiguelsPizza/webmcp-conformance/actions/workflows/check.yml/badge.svg)](https://github.com/MiguelsPizza/webmcp-conformance/actions/workflows/check.yml)
[![Docs](https://img.shields.io/badge/docs-model%20%26%20proofs-blue)](https://miguelspizza.github.io/webmcp-conformance/)

An executable model of the [WebMCP spec](https://webmachinelearning.github.io/webmcp/) in Lean 4, machine-checked proofs about that model, and a harness that runs the same random API-call sequences against implementations (today the polyfill and Chromium builds), compares each call with the model, and shrinks every disagreement to a minimal repro. The aim is one concrete target for implementers instead of each reading the prose differently. The approach follows [Cedar](https://github.com/cedar-policy/cedar-spec): a small, readable model that is both executable and the subject of proofs, used as the oracle for differential random testing.

- **[API docs](https://miguelspizza.github.io/webmcp-conformance/)**: every definition of the model and every theorem statement, browsable, with links to the source ([`WebMCP.Model`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Model.html), [`WebMCP.Proofs`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html))
- **[RESULTS.md](RESULTS.md)**: what each implementation did against the model, with repros
- **[docs/spec-mapping.md](docs/spec-mapping.md)**: each spec algorithm's definitions, theorems and examples

## Main results

All in [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean), about the model at spec commit [`14b6d53`](spec/anchors.json). The central one is an invariant of every state reachable by any sequence of calls, in every branch the spec allows for calls in flight: names are unique per document, a tool id identifies one registration, every registered tool is valid and lives in a document allowed to use "tools", and every `Tool` object's name, `source` and `origin` match the registration its tool id points to. The rest follow from it.

| Statement | Lean |
|---|---|
| The invariant holds in every reachable state, and every branch of an `Op.concurrent` keeps it. Every other operation has exactly one outcome. | [`reachable_invariant`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.reachable_invariant) ([L647](WebMCP/Proofs.lean#L647)), [`concurrent_spec`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.concurrent_spec) ([L563](WebMCP/Proofs.lean#L563)), [`step_deterministic`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.step_deterministic) ([L621](WebMCP/Proofs.lean#L621)) |
| **A tool is only discovered by an origin it is exposed to.** Every `Tool` `getTools()` returns comes from a document allowed to use "tools" that is same origin with the caller or in its `fromOrigins`, and is exposed to the caller's origin. | [`getTools_exposed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_exposed) ([L747](WebMCP/Proofs.lean#L747)), [`getTools_same_origin`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_same_origin) ([L765](WebMCP/Proofs.lean#L765)), [`getTools_not_from_disallowed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_not_from_disallowed) ([L820](WebMCP/Proofs.lean#L820)) |
| **A tool never runs for an origin it is not exposed to.** An awaited `executeTool()` on it rejects with `NotAllowedError`, `TypeError` or `NotFoundError` before the callback runs. Started in an `Op.concurrent` alongside any other calls, it rejects with one of those or `AbortError` in every order, and its queued tool execute steps leave the page unchanged. | [`executeTool_not_exposed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.executeTool_not_exposed) ([L888](WebMCP/Proofs.lean#L888)), [`concurrent_not_exposed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.concurrent_not_exposed) ([L1161](WebMCP/Proofs.lean#L1161)), [`asyncStep_not_exposed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.asyncStep_not_exposed) ([L912](WebMCP/Proofs.lean#L912)) |
| **The spec's assertions hold.** In a document allowed to use "tools", once the input is serialized, `executeTool()` rejects with `NotFoundError` or runs exactly the registration the `Tool` names, in the document of its `origin`; "unregister a tool" finds the tool; `registerTool()`'s signal is not aborted. | [`execute_assert_name`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.execute_assert_name) ([L1241](WebMCP/Proofs.lean#L1241)), [`unregister_assert_exists`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregister_assert_exists) ([L704](WebMCP/Proofs.lean#L704)), [`registerTool_assert_signal`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.registerTool_assert_signal) ([L694](WebMCP/Proofs.lean#L694)) |
| **A `Tool` whose registration is gone never runs anything again**: it fails with `NotFoundError` (or earlier `TypeError`/`NotAllowedError`), even if a new tool takes its name. | [`stale_tool_not_found`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.stale_tool_not_found) ([L1291](WebMCP/Proofs.lean#L1291)) |
| **Unregistration racing execution.** For the script `executeTool(tool, input)` with no `signal`, then aborting the signal `tool`'s registration was made with, then `registerTool(t)` with no `signal` or `exposedTo` (any name, such as the old one), in one document, every order rejects the execution with `NotFoundError` (or an earlier `NotAllowedError` or `TypeError`), settles the abort, and settles the registration as it would right after the unregistration. | [`unregistration_execution_race`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregistration_execution_race) ([L1326](WebMCP/Proofs.lean#L1326)) |
| **Aborting an execution.** For `executeTool(tool, input, {signal})` then `controller.abort()`, in a document allowed to use "tools" and with an input that serializes, every order rejects the call with `AbortError` and settles the abort. | [`cancel_rejects`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.cancel_rejects) ([L1390](WebMCP/Proofs.lean#L1390)) |
| A tool that unregisters itself still completes, and is gone afterwards. | [`unregisterSelf_completes`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregisterSelf_completes) ([L1406](WebMCP/Proofs.lean#L1406)) |
| `getTools()` is sorted by name with unique names; a fulfilled `registerTool()` shows up in the next `getTools()` with what was passed in; aborting a signal removes exactly its tools; a rejected `registerTool()` changes nothing. | [`getTools_sorted`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_sorted), [`getTools_names_unique`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_names_unique), [`registerTool_then_getTools`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.registerTool_then_getTools), [`unregisterBySignal_tools`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregisterBySignal_tools), [`registerTool_err_state`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.registerTool_err_state) |

[`WebMCP/Examples.lean`](WebMCP/Examples.lean) checks hand-written traces against the outcomes the spec requires.

## Findings at a glance

Proofs say nothing directly about implementations; testing is the link. Each implementation replayed the recorded corpus of 1,000 sequences (6,146 calls). Details, repros and the full table are in [RESULTS.md](RESULTS.md).

| Implementation | Against the model |
|---|---|
| Polyfill [PR #25](https://github.com/w3c-oss/webmcp-polyfill/pull/25) (63ddbfd) | Agrees on 6,123 calls. The other 23 are two bugs: permissions policy checked after the arguments, and duplicate names found late within one script |
| Polyfill main (4c01562) | Those two, plus two that PR #25 fixes (dictionaries instead of `Tool` objects, and a stale `Tool` running a re-registered tool) and an aborted execution not running its callback, which may be a spec issue |
| Chrome Canary 160.0.8177.0 (hand run) | Agrees on every call except the open spec question [#361](https://github.com/webmachinelearning/webmcp/issues/361): result strings aren't JSON-encoded |
| Chromium 157.0.8103.78 (Playwright's) | #361 plus 5 root causes of version lag, all fixed in Canary, and an intermittent hang in one frame |
| Chrome 157.0.8103.80 (hand run) | #361 plus 4 of those 5 root causes |

Against the official web-platform-tests, 89 of 211 subtests can be translated into the model, and it agrees with every assertion it can express except the 13 that turn on #361 ([wpt/README.md](wpt/README.md)). Where WPT and the spec disagree, the model follows the spec.

## What is trusted

- **The Lean kernel** (Lean 4.36.0, no other dependencies). The build runs with `--wfail`, so no `sorry` gets through, and 23 theorems carry `#guard_msgs in #print axioms` pinning them to the three standard axioms `propext`, `Classical.choice` and `Quot.sound` (end of [`Proofs.lean`](WebMCP/Proofs.lean#L1422)); [`check.sh`](.github/spec-update/check.sh) rejects any other axiom, in CI.
- **The transcription.** [`WebMCP/Model.lean`](WebMCP/Model.lean) is a hand transcription of the spec prose, each definition citing the algorithm it models. It has not been reviewed by the spec editors or anyone else, and the theorems are only as meaningful as it is. [`tools/check-spec.cjs`](tools/check-spec.cjs) catches upstream changes to the cited text ([`spec/anchors.json`](spec/anchors.json)), not mistakes in reading it.
- **The abstractions.** One fixed frame tree, author-supplied values from small fixed sets, and the other simplifications listed in the header of `Model.lean` (see [Scope](#scope)). The proofs say nothing outside them.
- **Unverified code.** The oracle's JSON parsing ([`Oracle.lean`](WebMCP/Oracle.lean), [`Main.lean`](Main.lean)) and the harness ([`harness/run.cjs`](harness/run.cjs)) are ordinary code with no proofs; the WPT translation is by hand, recorded subtest by subtest.
- **Testing is not proof.** A pass means an implementation matched the model on every generated sequence, not that it is correct. Each disagreement needs a person to decide whether the implementation, the spec or the model is wrong; when every implementation disagrees the same way, suspect the model or the spec first.

## Scope

A fixed frame tree of five documents on three origins (`harnessDocs` in [`WebMCP/Model.lean`](WebMCP/Model.lean)), one of them a cross-origin `<iframe>` that doesn't delegate "tools". The model covers `registerTool()` (Web IDL conversion, validation in spec order, schemas, `exposedTo`, unregistration through the signal, permissions policy), `getTools()` (`fromOrigins`, which documents and tools the caller sees, the members of each `Tool`, order), `executeTool()` (lookup in the `Tool`'s source document, the exposure check, input, results and errors), and calls started from one script before any is awaited (`Op.concurrent`), including aborting an execution's `signal`, with every outcome the spec's ordering allows. Author-supplied values come from small fixed sets.

Not modelled yet: events, the callback's own `signal`, calls from several documents' scripts at once, callbacks that do more than settle or unregister their own tool, navigation and unloading, documents in other traversables, opaque origins, and other frame trees. The header of `Model.lean` lists every simplification.

## Building and checking

Lean 4.36.0 is pinned in [`lean-toolchain`](lean-toolchain); [elan](https://github.com/leanprover/elan) picks it up. There are no Lake dependencies, so there is no cache to fetch.

```
lake build                             # the model, the proofs and the oracle
lake test                              # the corpus and repros still match the model; no browser
bash .github/spec-update/check.sh      # everything the Check workflow runs, including the axiom check
```

Replay the corpus against an implementation, without Lean (Node 22):

```
npm install && npx playwright install chromium
node harness/run.cjs chromium --replay corpus/spec-14b6d53.json   # or polyfill:<path to dist/polyfill.js>
```

## Layout

| Path | What it is |
|---|---|
| [`WebMCP/Model.lean`](WebMCP/Model.lean) | The model; each definition cites the spec algorithm it transcribes |
| [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean), [`WebMCP/Examples.lean`](WebMCP/Examples.lean) | The proofs, and hand-written traces with the outcomes the spec requires |
| [`WebMCP/Oracle.lean`](WebMCP/Oracle.lean), [`Main.lean`](Main.lean), [`ReplayTest.lean`](ReplayTest.lean) | The oracle (JSON traces in, the spec's outcomes out) and `lake test` |
| [`harness/`](harness/run.cjs), [`corpus/`](corpus/README.md), [`expectations/`](expectations/README.md), [`results/`](results/README.md) | The harness, the recorded traces, known divergences per target, and machine-written results |
| [`repros/`](repros), [`wpt-export/`](wpt-export/README.md) | One minimal trace per finding, and the same as WPT tests |
| [`wpt/`](wpt/README.md) | The model scored against web-platform-tests |
| [`spec/anchors.json`](spec/anchors.json), [`tools/`](tools) | The spec commit modelled and a hash of each passage, and the scripts that check them |
| [`docbuild/`](docbuild) | The doc-gen4 build behind the API docs |

Further reading: [docs/reading-lean.md](docs/reading-lean.md) (reading `Model.lean` without knowing Lean), [docs/harness.md](docs/harness.md) (targets, generating and shrinking traces, comparing outcomes, expectations, the WPT export), [docs/maintaining.md](docs/maintaining.md) (building the docs, keeping the model current with the spec).

## License

[MIT](LICENSE)
