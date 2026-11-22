# WebMCP conformance: a Lean reference model

An executable model of the [WebMCP spec](https://webmachinelearning.github.io/webmcp/), written in Lean 4, with machine-checked proofs about it and a harness that runs the same randomly generated API-call sequences against every WebMCP implementation it can reach. Each implementation gets compared against the model call by call, and every disagreement is shrunk to a minimal repro.

The aim is to give implementers one concrete target instead of each reading the prose differently. See [RESULTS.md](RESULTS.md) for where the polyfill and Chromium stand today.

## Scope

The model covers one slice of the spec (upstream commit 14b6d53), for a single document with same-origin callers:

- `registerTool()`: validation order, duplicate names, schema serialization, abort-signal unregistration
- `getTools()`: which tools are returned, sorted by name
- `executeTool()`: lookup by tool id, input and result serialization, and the platform error outcomes

Not modelled yet: cross-frame and cross-origin exposure (`exposedTo`, `fromOrigins`), events, execution cancellation and other timing races, Web IDL conversion details, and permissions policy.

## What's proved

[`WebMCP/Proofs.lean`](WebMCP/Proofs.lean) proves, for every state and every sequence of calls:

- tool names in a document stay unique, and every registered tool has a valid name and a non-empty description (`run_inv`)
- `getTools()` never returns two tools with the same name (`getTools_names_unique`)
- tool ids are never reused, so a `Tool` whose registration is gone fails with `NotFoundError` forever, even if a new tool takes its name (`stale_handle_not_found`)

The proofs use only Lean's standard axioms (`#print axioms` at the end of the file).

## What this does and doesn't guarantee

- The proofs are about the model. They show the spec's algorithms, as transcribed here, keep those properties. They say nothing directly about any implementation.
- The link to implementations is testing. A pass means the implementation matched the model on every generated sequence, not that it is correct.
- The model is a transcription of spec prose. Each definition cites the step it models so a misreading is easy to spot, but any disagreement still needs a person to decide whether the implementation, the spec, or the model is wrong.

## Running it

Needs Lean 4.25.0 and Node with Playwright.

```
lake build                                         # checks the proofs, builds the oracle
node harness/run.cjs <target> [traces=300] [seed=1]
```

`<target>` is `polyfill:<path to dist/polyfill.js>`, `chromium` (native WebMCP behind `--enable-blink-features=WebMCP`), or `chromium:<path to a chrome binary>` for another build such as Canary.

## Keeping it current

When the spec changes an algorithm, update the matching function in [`WebMCP/Model.lean`](WebMCP/Model.lean). If the change breaks a proved property, the proof that stops compiling says which one. Then rerun the harness to see which implementations have caught up.
