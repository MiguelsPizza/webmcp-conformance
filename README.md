# WebMCP conformance in Lean

[![Check](https://github.com/MiguelsPizza/webmcp-conformance/actions/workflows/check.yml/badge.svg)](https://github.com/MiguelsPizza/webmcp-conformance/actions/workflows/check.yml)
[![Docs](https://img.shields.io/badge/docs-model%20%26%20proofs-blue)](https://miguelspizza.github.io/webmcp-conformance/)

[WebMCP](https://webmachinelearning.github.io/webmcp/) lets a web page register tools that an AI agent can call. Each implementation has to work out on its own what the spec prose means.

This repo writes the spec as a Lean 4 program, proves things about that program, and uses it to test implementations. A harness runs the same random sequences of API calls in a browser and in the model, and reports every call where they disagree. So far I've run it against Chrome and the [polyfill](https://github.com/w3c-oss/webmcp-polyfill). The point is to show instead of tell, and let implementers have a real target to match against.

I borrowed the setup from [Cedar](https://github.com/cedar-policy/cedar-spec), which does the same for its policy language. Every definition and theorem is browsable in the [API docs](https://miguelspizza.github.io/webmcp-conformance/) ([`WebMCP.Model`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Model.html), [`WebMCP.Proofs`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html)).

## What it found

Each implementation replayed the same 1,000 recorded sequences (6,146 calls). [RESULTS.md](RESULTS.md) has the details and a minimal repro for each finding.

- Chrome Canary 160 agrees on every call except one open spec question, [#361](https://github.com/webmachinelearning/webmcp/issues/361): should `executeTool()` return a tool's result JSON-encoded (`"hi"`), as the spec says, or as a plain string (`hi`), as Chrome does? WPT currently follows Chrome.
- The polyfill at [PR #25](https://github.com/w3c-oss/webmcp-polyfill/pull/25) (63ddbfd) agrees on 6,123 calls. The other 23 come from two bugs. It checks the "tools" permissions policy after the arguments, so a frame without that permission gets the wrong error. And when one script registers the same name twice without awaiting, it notices the duplicate too late.
- Polyfill main (4c01562) also returns plain dictionaries instead of `Tool` objects, and an old `Tool` can run a newer tool that reused its name. PR #25 fixes both.
- When you abort `executeTool()`'s signal, both polyfill builds skip the tool's callback. The spec rejects with `AbortError` but still runs the callback, and Chromium 157 runs it too. I suspect this is a spec issue rather than a polyfill bug.
- Chromium 157 (Playwright's 157.0.8103.78) has #361 plus five places where it still follows an older draft of the spec, such as `UnknownError` where the spec now says `OperationError` or `NotFoundError`. Canary fixes all five, and a hand run on Chrome 157.0.8103.80 hit four of them. Separately, `getTools()` and `registerTool()` sometimes never settle in one of the frames.

I also scored the model against the official web-platform-tests. 89 of the 211 subtests fall within what the model covers, and the model agrees with every assertion in them it can express, except 13 that depend on #361 ([wpt/README.md](wpt/README.md)). Where WPT and the spec disagree, the model follows the spec.

## What to trust

The model is my hand transcription of the spec, and nobody else has reviewed it yet. Every proof is about the model, so if I misread the spec, the theorems prove the wrong thing. If you know the spec, a check of [`Model.lean`](WebMCP/Model.lean) against the prose would help a lot. Each definition cites the algorithm it transcribes, [docs/spec-mapping.md](docs/spec-mapping.md) maps each spec section to its Lean, and [docs/reading-lean.md](docs/reading-lean.md) covers enough Lean to follow along. [`tools/check-spec.cjs`](tools/check-spec.cjs) flags when the cited spec text changes upstream ([`spec/anchors.json`](spec/anchors.json)). It can't catch a misreading.

The proofs are checked by Lean 4.36.0 with no other dependencies. The build fails on any warning, so there's no `sorry`, and CI checks that every theorem named below uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The proofs are about a simplified model, with one fixed frame tree and author-supplied values from small fixed sets (see [Scope](#scope)), and say nothing outside it.

The oracle's JSON parsing ([`Oracle.lean`](WebMCP/Oracle.lean), [`Main.lean`](Main.lean)), the harness ([`harness/run.cjs`](harness/run.cjs)) and the WPT translation are ordinary code with no proofs.

Testing only shows that an implementation matched the model on the sequences we ran, not that it's correct. Each mismatch needs a person to decide whether the implementation, the spec or the model is wrong. When every implementation disagrees with the model in the same way, I'd look at the model and the spec first.

## Testing your implementation

You don't need Lean. The corpus records the model's expected outcome for every call, so replaying it only takes Node 22 and Playwright:

```
npm install && npx playwright install chromium
node harness/run.cjs chromium --replay corpus/spec-14b6d53.json
```

The first argument is the target:

- `chromium` is Playwright's bundled Chromium (157.0.8103.78), with WebMCP turned on.
- `chromium:<path to a Chrome binary>` is any other Chromium build, such as Canary or your own.
- `polyfill:<path to dist/polyfill.js>` injects the polyfill into Playwright's Chromium.

Here's the output for polyfill PR #25:

```
target polyfill:polyfill-pr25/dist/polyfill.js, browser 157.0.8103.78, polyfill 0.1.1 at 63ddbfd
expectations expectations/polyfill.json: 4 apply
1000 traces, 6146 operations, 6146 compared: 6123 agree, 23 expected divergences, 0 unexpected
  expected    21  polyfill-policy-checked-after-arguments
  expected     2  polyfill-duplicate-name-checked-late
no unexpected divergences
```

Known divergences, like #361, live in [`expectations/`](expectations/README.md) per browser family and version, and are counted by id instead of failing the run. Any other mismatch prints the shortest failing sequence with the spec's and the implementation's outcome for each call, and the run exits non-zero. `--results <file>` also saves the run as JSON.

With Lean installed, `node harness/run.cjs <target> [traces] [seed]` generates fresh sequences and shrinks each mismatch to a minimal repro. If you'd rather use your own WPT setup, [`wpt-export/`](wpt-export/README.md) has the single-document findings as ready-made WPT tests.

Firefox and WebKit have no target yet. The harness launches Chromium through Playwright, so a new target means launching another browser with WebMCP turned on; [docs/harness.md](docs/harness.md) explains how targets and comparisons work. Firefox's prototype still exposes an earlier API ([RESULTS.md](RESULTS.md#firefox)), so most of the spec isn't there to compare yet.

## Main results

The proofs are in [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean), about the model at spec commit [`14b6d53`](spec/anchors.json). A state is reachable if some sequence of calls gets there from an empty page, in any order the spec allows. A tool is exposed to an origin if it's that origin's own tool or lists the origin in `exposedTo`. A document is allowed to use tools if the "tools" permissions policy lets it. According to the model, the spec guarantees that:

- In every reachable state, tool names are unique within a document, every registered tool is valid and lives in a document allowed to use tools, and every `Tool` object's name, `source` and `origin` match the registration it points to.
- `getTools()` only returns tools exposed to the caller's origin, from documents allowed to use tools that are same origin with the caller or listed in `fromOrigins`.
- A tool never runs for an origin it isn't exposed to. `executeTool()` rejects before the callback runs, also when started alongside other calls.
- A `Tool` whose registration is gone never runs anything again, even if a new tool takes its name.
- The spec's three `Assert` steps can never fail.
- The races described in the spec's notes come out as the notes say: unregistering a tool while it executes, aborting an execution, and a tool that unregisters itself.

For Lean readers, here are the central theorem and the exposure check for one awaited call. `run {} ops` is every way the calls `ops` can play out from an empty page, and `Invariant` includes everything in the first bullet. If the registration behind `tool` isn't exposed to the origin of caller `c`, `executeTool()` rejects with one of three errors:

```lean
theorem reachable_invariant (ops : List Op) : ∀ p ∈ run {} ops, Invariant p.1

theorem executeTool_not_exposed {s : State} {call k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) (x : Input) (c : Nat)
    (hnot : ∀ d ∈ s.tools, d.id = tool.id →
      toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s c) = false) :
    (executeTool s call k x c).2 = .err .notAllowed ∨
    (executeTool s call k x c).2 = .err .typeError ∨
    (executeTool s call k x c).2 = .err .notFound
```

The rest: [`concurrent_spec`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.concurrent_spec), [`step_deterministic`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.step_deterministic), [`getTools_exposed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_exposed), [`getTools_same_origin`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_same_origin), [`getTools_not_from_disallowed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_not_from_disallowed), [`concurrent_not_exposed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.concurrent_not_exposed), [`asyncStep_not_exposed`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.asyncStep_not_exposed), [`stale_tool_not_found`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.stale_tool_not_found), [`execute_assert_name`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.execute_assert_name), [`unregister_assert_exists`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregister_assert_exists), [`registerTool_assert_signal`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.registerTool_assert_signal), [`unregistration_execution_race`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregistration_execution_race), [`cancel_rejects`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.cancel_rejects), [`unregisterSelf_completes`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregisterSelf_completes), [`getTools_sorted`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_sorted), [`getTools_names_unique`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.getTools_names_unique), [`registerTool_then_getTools`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.registerTool_then_getTools), [`unregisterBySignal_tools`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.unregisterBySignal_tools), [`registerTool_err_state`](https://miguelspizza.github.io/webmcp-conformance/WebMCP/Proofs.html#WebMCP.registerTool_err_state). Each docstring says what it states. [`WebMCP/Examples.lean`](WebMCP/Examples.lean) checks hand-written traces against the outcomes the spec requires.

## Scope

Covered:

- A fixed frame tree of five documents on three origins (`harnessDocs` in [`Model.lean`](WebMCP/Model.lean)), one of them a cross-origin `<iframe>` that doesn't delegate "tools"
- `registerTool()`: Web IDL conversion, validation in spec order, schemas, `exposedTo`, unregistration through the signal, permissions policy
- `getTools()`: `fromOrigins`, which documents and tools the caller sees, the members of each `Tool`, order
- `executeTool()`: lookup in the `Tool`'s source document, the exposure check, input, results and errors
- Calls started from one script before any is awaited (`Op.concurrent`), including aborting an execution's signal, in every order the spec allows

Not covered yet:

- Events, and the callback's own `signal`
- Calls from several documents' scripts at once
- Callbacks that do more than settle or unregister their own tool
- Navigation and unloading, documents in other traversables, opaque origins, other frame trees

Author-supplied values come from small fixed sets. The header of `Model.lean` lists every simplification.

## Building and checking

Lean 4.36.0 is pinned in [`lean-toolchain`](lean-toolchain), and [elan](https://github.com/leanprover/elan) picks it up. There are no Lake dependencies, so there's no cache to fetch.

```
lake build                             # the model, the proofs and the oracle
lake test                              # the corpus and repros still match the model; no browser
bash .github/spec-update/check.sh      # everything the Check workflow runs, including the axiom check
```

## Layout

| Path | What it is |
|---|---|
| [`WebMCP/Model.lean`](WebMCP/Model.lean) | The model; each definition cites the spec algorithm it transcribes |
| [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean), [`WebMCP/Examples.lean`](WebMCP/Examples.lean) | The proofs, and hand-written traces with the outcomes the spec requires |
| [`WebMCP/Oracle.lean`](WebMCP/Oracle.lean), [`Main.lean`](Main.lean), [`ReplayTest.lean`](ReplayTest.lean) | The oracle (JSON traces in, the spec's outcomes out) and `lake test` |
| [`harness/`](harness/run.cjs), [`corpus/`](corpus/README.md), [`expectations/`](expectations/README.md), [`results/`](results/README.md) | The harness, the recorded sequences, known divergences per target, and machine-written results |
| [`repros/`](repros), [`wpt-export/`](wpt-export/README.md), [`wpt/`](wpt/README.md) | One minimal trace per finding, the same as WPT tests, and the model scored against web-platform-tests |
| [`spec/anchors.json`](spec/anchors.json), [`tools/`](tools) | The spec commit modelled and a hash of each cited passage, and the scripts that check them |
| [`docs/`](docs) | [Reading the model without Lean](docs/reading-lean.md), [the harness](docs/harness.md), [maintaining the model and docs](docs/maintaining.md) |
| [`docbuild/`](docbuild) | The doc-gen4 build behind the API docs |

Feedback very welcome, especially if you spot a place where the model and the spec disagree.

## License

[MIT](LICENSE)
