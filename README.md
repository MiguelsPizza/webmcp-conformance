# WebMCP conformance: a Lean reference model

An executable model of the [WebMCP spec](https://webmachinelearning.github.io/webmcp/), written in Lean 4, with machine-checked proofs about it and a harness that runs the same randomly generated API-call sequences against every WebMCP implementation it can reach. Each implementation gets compared against the model call by call, and every disagreement is shrunk to a minimal repro.

The aim is to give implementers one concrete target instead of each reading the prose differently. See [RESULTS.md](RESULTS.md) for where the polyfill and Chromium stand today.

The approach follows [Cedar](https://github.com/cedar-policy/cedar-spec): a small, readable Lean model that is both executable and the subject of proofs, used as the oracle for differential random testing against real implementations.

## Layout

| Path | What it is |
|---|---|
| [`WebMCP/Model.lean`](WebMCP/Model.lean) | The model. Each definition cites the spec algorithm it transcribes (`Spec: #anchor`), and the file lists every simplification it makes. |
| [`WebMCP/Proofs.lean`](WebMCP/Proofs.lean) | Proofs about the model. The build fails if any of them rests on `sorry`. |
| [`WebMCP/Examples.lean`](WebMCP/Examples.lean) | Hand-written traces with the outcomes the spec requires, including the spec's own examples, checked at build time. |
| [`Main.lean`](Main.lean) | The oracle: JSON traces in, the spec's outcomes out. |
| [`harness/run.cjs`](harness/run.cjs) | Generates traces, runs them in a browser, compares, shrinks. |
| [`corpus/`](corpus) | 1,000 recorded traces with expected outcomes, for running without Lean. |
| [`spec/anchors.json`](spec/anchors.json), [`tools/check-spec.cjs`](tools/check-spec.cjs) | The spec commit the model reflects, and a hash of each part of `index.bs` it transcribes. |

## Scope

The model covers one slice of the spec, for a single document with same-origin callers:

- `registerTool()`: Web IDL conversion failures, the validation steps in spec order, schema serialization, and unregistration through the registration signal, including aborting it before the call's promise settles
- `getTools()`: every registered tool, sorted by name, with the `name`, `title`, `description`, `inputSchema`, `outputSchema` and `annotations` each `Tool` exposes
- `executeTool()`: lookup by tool id, input serialization and "invalid input", and how each kind of callback outcome becomes a result string or an exception

Not modelled yet: cross-frame and cross-origin exposure (`exposedTo`, `fromOrigins`), events, the execution `signal`, interleavings of calls that run in parallel or from queued tasks, and permissions policy.

## What's proved

[`WebMCP/Proofs.lean`](WebMCP/Proofs.lean) proves, for every state reachable by any sequence of calls (`reachable_invariant`):

- tool names stay unique, and a tool id identifies one registration
- every registered tool has a valid name, a non-empty description, and a registration signal that hasn't fired
- every `Tool` object's name is the name of the registration its tool id points to

From those:

- **The spec's `executeTool()` assertion always holds** (`execute_assert_name`). When a `Tool`'s registration is still in the tool map, the definition found there has the `Tool`'s name, so the call runs exactly the registration `getTools()` returned.
- **A `Tool` whose registration is gone can never run anything again** (`stale_handle_not_found`). It fails with `NotFoundError` even if a new tool takes its name. This is the guarantee spec PR #348 introduced the `Tool` interface for.
- `getTools()` never returns two tools with the same name (`getTools_names_unique`).
- A rejected `registerTool()` leaves the tool map unchanged (`register_failure_no_effect`).

## How implementations are compared

- Every call that returns a promise must return one. A synchronous throw is reported as `threw:` and doesn't count as a rejection.
- An exception matches only if it is a real `DOMException` (or `TypeError`) with the expected name.
- Each call has a 5-second timeout, so an implementation that never settles a promise shows up as `timeout` instead of hanging the run.
- `--known` treats the result-serialization differences in spec issue #361 as equal and counts them, so they don't hide other bugs later in the same trace.

## What this does and doesn't guarantee

- The proofs are about the model. They show the spec's algorithms, as transcribed here, keep those properties. They say nothing directly about any implementation.
- The link to implementations is testing. A pass means the implementation matched the model on every generated sequence, not that it is correct.
- The model is a transcription of spec prose. Every disagreement needs a person to decide whether the implementation, the spec, or the model is wrong. When every implementation disagrees with the model the same way, suspect the model or the spec first.

## Running it

Every implementation can be checked without Lean, against the recorded corpus:

```
npm install                                                     # Playwright only
node harness/run.cjs <target> --replay corpus/spec-14b6d53.json
```

`<target>` is one of:

- `polyfill:<path to dist/polyfill.js>`: the polyfill, injected into Playwright's Chromium
- `chromium`: Chromium's native WebMCP, behind `--enable-blink-features=WebMCP`
- `chromium:<path to a chrome binary>`: the same for another build, such as Canary

With Lean 4.25.0 you can also check the proofs, generate fresh traces, and shrink any disagreement to a minimal repro:

```
lake build                                          # proofs, examples, oracle
node harness/run.cjs <target> [traces=300] [seed=1]
node harness/run.cjs --record <corpus.json> [traces] [seed]   # also prints outcome coverage
```

## Keeping it current

`node tools/check-spec.cjs <path to index.bs>` re-extracts each part of the spec the model transcribes and fails if its text changed since the commit in `spec/anchors.json`. For each changed part, update the definitions that cite it, then:

1. `lake build`. If a proved property no longer holds, the proof that stops compiling says which one.
2. `node tools/check-spec.cjs <index.bs> --update <sha>`.
3. Re-record the corpus.
4. Rerun the harness to see which implementations have caught up.
