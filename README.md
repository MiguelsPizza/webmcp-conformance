# WebMCP conformance: a Lean reference model

An executable model of the [WebMCP spec](https://webmachinelearning.github.io/webmcp/), written in Lean 4, with machine-checked proofs about it and a harness that runs the same randomly generated API-call sequences against WebMCP implementations: today the polyfill and Chromium builds. Each implementation gets compared against the model call by call, and every disagreement is shrunk to a minimal repro.

The aim is to give implementers one concrete target instead of each reading the prose differently. See [RESULTS.md](RESULTS.md) for where the polyfill and Chromium stand today.

The approach follows [Cedar](https://github.com/cedar-policy/cedar-spec): a small, readable Lean model that is both executable and the subject of proofs, used as the oracle for differential random testing against real implementations.

## Layout

| Path | What it is |
|---|---|
| [`WebMCP/Model.lean`](WebMCP/Model.lean) | The model. Each definition cites the spec algorithm it transcribes (`Spec: #anchor`), and the file lists every simplification it makes. |
| [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean) | Proofs about the model. The build fails if any of them rests on `sorry`. |
| [`WebMCP/Examples.lean`](WebMCP/Examples.lean) | Hand-written traces with the outcomes the spec requires, including the spec's own examples, checked at build time. |
| [`WebMCP/Oracle.lean`](WebMCP/Oracle.lean), [`Main.lean`](Main.lean) | The oracle: JSON traces in, the spec's outcomes out. `Oracle.lean` has the wire format, `Main.lean` the loop over stdin. |
| [`harness/run.cjs`](harness/run.cjs) | Generates traces, runs them in a browser, compares, shrinks. |
| [`corpus/`](corpus) | 1,000 recorded traces with expected outcomes, for running without Lean. |
| [`wpt/`](wpt/README.md), [`tools/wpt-score.cjs`](tools/wpt-score.cjs) | The model scored against the official web-platform-tests for WebMCP: each in-scope subtest translated to a trace. |
| [`expectations/`](expectations) | Known divergences per target family (#361, and version lag), counted instead of failing. |
| [`results/`](results) | Machine-written results of each run: versions, counts, and the trace for each unexpected divergence. |
| [`repros/`](repros) | One minimal trace per finding in RESULTS.md, with what each implementation does. |
| [`wpt-export/`](wpt-export), [`tools/export-wpt.cjs`](tools/export-wpt.cjs), [`tools/run-wpt-export.cjs`](tools/run-wpt-export.cjs) | The repros as WPT testharness.js tests (not submitted), and a Playwright runner for them. |
| [`ReplayTest.lean`](ReplayTest.lean) | `lake test`: replays the corpus and repros through the oracle. |
| [`spec/anchors.json`](spec/anchors.json), [`tools/check-spec.cjs`](tools/check-spec.cjs) | The spec commit the model reflects, and a hash of each part of `index.bs` it transcribes. |

## Reading the Lean

You don't need to know Lean to follow `WebMCP/Model.lean` against the spec. Each definition's docstring names the spec algorithm (`Spec: #anchor`), and each check inside it quotes the step it models. The module doc at the top of the file has a table from spec terms (tool definition, `Tool`, tool id, tool execution error) to Lean names, and [Spec mapping](#spec-mapping) below goes from each spec anchor to its definitions, theorems and examples. The syntax that comes up most:

| Lean | Roughly, in JavaScript |
|---|---|
| `def f (s : State) (t : ModelContextTool) : Outcome := ...` | `function f(s, t) { return ... }`, with types |
| `structure ToolDef where id : Nat ...` | a plain object type with those fields |
| `inductive Err where \| typeError \| abort ...` | an enum (each case can carry data) |
| `.err .abort` | `{kind: "err", error: "AbortError"}` |
| `Except ToolExecutionError String`, `.ok r`, `.error e` | a result `r` or a failure reason `e`, like a settled promise |
| `Option String`, `some x`, `none` | a value that may be absent: `x` or `null` |
| `match x with \| some v => a \| none => b` | `x != null ? a : b`, with `v = x` |
| `{ s with tools := ts }` | `{...s, tools: ts}` |
| `(·.name)` | `t => t.name` |
| `⟨d.id, d.name⟩` | build a structure from its fields in order: `{id: d.id, name: d.name}` |
| `l[i]?` | `l[i]`, giving `none` when out of range |
| `xs.filter p`, `xs.find? p`, `xs.map f` | `xs.filter(p)`, `xs.find(p)`, `xs.map(f)` |
| `a && b`, `!a`, `==`, `!=` | the same as in JavaScript |

`Proofs.lean` is harder going and you don't need to read the proofs: each theorem's docstring says in English what it shows, and Lean checks the proof when the project builds.

## Scope

The model covers one slice of the spec, for a single document with same-origin callers:

- `registerTool()`: Web IDL conversion failures, the validation steps in spec order, schema serialization, and unregistration through the registration signal, including aborting it before the call's promise settles
- `getTools()`: every registered tool, sorted by name, with the `name`, `title`, `description`, `inputSchema`, `outputSchema` and `annotations` each `Tool` exposes
- `executeTool()`: lookup by tool id, input serialization and "invalid input", and how each kind of callback outcome becomes a result string or an exception

Author-supplied values (schemas, callback behaviours, inputs) come from small fixed sets, listed in `WebMCP/Model.lean`, not arbitrary JavaScript values.

Not modelled yet: cross-frame and cross-origin exposure (`exposedTo`, `fromOrigins`), events, the execution `signal`, interleavings of calls that run in parallel or from queued tasks, and permissions policy.

## What's proved

[`WebMCP/Proofs.lean`](WebMCP/Proofs.lean) proves, for every state reachable by any sequence of calls (`reachable_invariant`):

- tool names stay unique, and a tool id identifies one registration
- every registered tool has a valid name, a non-empty description, and a registration signal that hasn't fired
- every `Tool` object's name is the name of the registration its tool id points to
- every abort step on a signal that hasn't fired yet targets a tool that is still registered

From those:

- **The spec's `executeTool()` assertion always holds** (`execute_assert_name`). Once `executeTool()` has serialized its input, it either rejects with `NotFoundError` or runs the execute steps of a registered definition with the `Tool`'s tool id and name, so the call runs exactly the registration `getTools()` returned.
- **The spec's "unregister a tool" assertion always holds** (`unregister_assert_exists`). When a registration signal fires for the first time, every tool its abort steps unregister is still in the tool map. The model records those abort steps (`State.abortSteps`) only so this can be stated; no outcome depends on the record.
- **A `Tool` whose registration is gone can never run anything again** (`stale_tool_not_found`). It fails with `NotFoundError` even if a new tool takes its name. This is the guarantee spec PR #348 introduced the `Tool` interface for.
- `getTools()` lists tools in strictly increasing order of name (`getTools_sorted`), so it never returns two with the same name (`getTools_names_unique`). The order is Lean's `String` order, which is the spec's code-unit order for the ASCII names `registerTool()` accepts.
- After `registerTool()` fulfills, a `getTools()` call made right after lists a tool with that name, and its title, description, schemas and annotations are the ones passed in (`registerTool_then_getTools`).
- Aborting a registration signal removes exactly the tools registered with that signal and keeps every other tool, in order (`unregisterBySignal_tools`).
- A rejected `registerTool()` leaves the tool map unchanged (`registerTool_err_state`).
- `registerTool()`'s `Assert: signal is not aborted` holds (`registerTool_assert_signal`). This one follows directly from the check just before it.

## Spec mapping

Where each part of the spec the model transcribes lives in the Lean. Theorems are in [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean); examples are the named `#guard`s in [`WebMCP/Examples.lean`](WebMCP/Examples.lean).

| Spec anchor | Lean definition | Theorems | Examples |
|---|---|---|---|
| [`#model-context-tool`](https://webmachinelearning.github.io/webmcp/#model-context-tool) | `ModelContextTool`, `converts` | | `validation-order` |
| [`#tool-definition`](https://webmachinelearning.github.io/webmcp/#tool-definition) | `ToolDef`, `newTool`, `validName` | `reachable_invariant` | `names` |
| [`#tool-interface`](https://webmachinelearning.github.io/webmcp/#tool-interface) | `ToolObject`, `ToolView`, `ToolDef.view` | `registerTool_then_getTools` | `listed-and-runs` |
| [`#serialize-a-tool-schema`](https://webmachinelearning.github.io/webmcp/#serialize-a-tool-schema) | `Schema.exposed` | | `sorted`, `schema-before-signal` |
| [`#dom-modelcontext-registertool`](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-registertool) | `registerTool`, `registerToolChecks`, `addTool`, `registerAbortSync` | `registerToolChecks_eq_none`, `registerTool_err_state`, `registerTool_then_getTools`, `registerTool_assert_signal` | `validation-order`, `schema-before-signal`, `abort-before-await`, `names` |
| [`#model-context-unregister-a-tool`](https://webmachinelearning.github.io/webmcp/#model-context-unregister-a-tool) | `unregisterBySignal` | `unregister_assert_exists`, `unregisterBySignal_tools` | `unregistration-execution-race`, `abort-before-await` |
| [`#dom-modelcontext-gettools`](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-gettools) | `getTools`, `sortTools` | `getTools_sorted`, `getTools_names_unique` | `sorted` |
| [`#dom-modelcontext-executetool`](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-executetool) | `executeTool`, `completionOutcome` | `execute_assert_name`, `stale_tool_not_found` | `unregistration-execution-race`, `results` |
| [`#tool-execute-steps`](https://webmachinelearning.github.io/webmcp/#tool-execute-steps) | `toolExecuteSteps` | `stale_tool_not_found` | `unregistration-execution-race` |
| [`#invoke-the-execute-callback`](https://webmachinelearning.github.io/webmcp/#invoke-the-execute-callback) | `invokeExecuteCallback`, `callbackResult` | | `listed-and-runs`, `results` |
| [`#tool-execution-error`](https://webmachinelearning.github.io/webmcp/#tool-execution-error) | `ToolExecutionError`, `ToolExecutionError.exceptionName` | | `results`, `unregistration-execution-race` |

## How implementations are compared

- Every call that returns a promise must return one. A synchronous throw is reported as `threw:` and doesn't count as a rejection.
- An exception matches only if it is a real `DOMException` (or `TypeError`) with the expected name.
- Each call has a 5-second timeout, so an implementation that never settles a promise shows up as `timeout` instead of hanging the run.
- A divergence listed in `expectations/<family>.json` (such as spec issue #361's result strings) is counted under its id and the trace goes on, so it doesn't hide other bugs later in the same trace. Any other divergence ends that trace, and makes the run exit non-zero. `--no-expectations` counts everything as unexpected.

## What this does and doesn't guarantee

- The proofs are about the model. They show the spec's algorithms, as transcribed here, keep those properties. They say nothing directly about any implementation.
- The link to implementations is testing. A pass means the implementation matched the model on every generated sequence, not that it is correct.
- The model is a transcription of spec prose. Every disagreement needs a person to decide whether the implementation, the spec, or the model is wrong. When every implementation disagrees with the model the same way, suspect the model or the spec first.

## Running it

Every implementation can be checked without Lean, against the recorded corpus:

```
npm install                                                     # Playwright only
npx playwright install chromium                                 # its bundled Chromium
node harness/run.cjs <target> --replay corpus/spec-14b6d53.json [--results results/<label>.json]
node harness/run.cjs <target> --replay repros/<finding>.json            # one finding
```

`<target>` is one of:

- `polyfill:<path to dist/polyfill.js>`: the polyfill, injected into Playwright's Chromium
- `chromium`: Playwright's bundled Chromium (157.0.8103.78 with Playwright 1.63.0), with its native WebMCP behind `--enable-blink-features=WebMCP`. The hand-run rows in RESULTS.md used real Chrome builds, through the next form.
- `chromium:<path to a chrome binary>`: the same for another build, such as Canary

With Lean 4.36.0 (pinned in `lean-toolchain`; no Mathlib) you can also check the proofs, generate fresh traces, and shrink any disagreement to a minimal repro:

```
lake build                                          # proofs, examples, oracle
lake test                                           # corpus and repros still match the model; no browser
node harness/run.cjs <target> [traces=300] [seed=1] [--results <file>]
node harness/run.cjs --record <corpus.json> [traces] [seed]   # also prints outcome coverage
```

To turn the repros into WPT tests and run them (see [`wpt-export/README.md`](wpt-export/README.md)):

```
node tools/export-wpt.cjs repros/*.json --focus
node tools/run-wpt-export.cjs <wpt checkout> <target>
```

## Keeping it current

`node tools/check-spec.cjs <path to index.bs>` re-extracts each part of the spec the model transcribes and fails if its text changed since the commit in `spec/anchors.json`. For each changed part, update the definitions that cite it, then:

1. `lake build`. If a proved property no longer holds, the proof that stops compiling says which one.
2. `node tools/check-spec.cjs <index.bs> --update <sha>`.
3. Re-record the corpus, and refresh the repros' outcomes with `node tools/refresh-repros.cjs`.
4. Rerun the harness to see which implementations have caught up.
