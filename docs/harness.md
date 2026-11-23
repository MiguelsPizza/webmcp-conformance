# The harness

[`harness/run.cjs`](../harness/run.cjs) generates call sequences (traces), asks the oracle for the outcomes the spec allows, runs the same traces in a browser against an implementation, compares call by call, and shrinks each disagreement to a minimal trace. The trace format is in [`corpus/README.md`](../corpus/README.md).

## Targets

`<target>` is one of:

- `polyfill:<path to dist/polyfill.js>`: the polyfill, injected into Playwright's Chromium
- `chromium`: Playwright's bundled Chromium (157.0.8103.78 with Playwright 1.63.0), with its native WebMCP behind `--enable-blink-features=WebMCP`. The hand-run rows in RESULTS.md used real Chrome builds, through the next form.
- `chromium:<path to a chrome binary>`: the same for another build, such as Canary

## Running

Every implementation can be checked without Lean, against the recorded corpus (`corpus/spec-<sha>.json`; the README's replay command names the current one):

```
npm install                                                     # Playwright only
npx playwright install chromium                                 # its bundled Chromium
node harness/run.cjs <target> --replay corpus/spec-<sha>.json [--results results/<label>.json]
node harness/run.cjs <target> --replay repros/<finding>.json    # one finding
```

With Lean 4.36.0 (pinned in `lean-toolchain`; no Mathlib) you can also generate fresh traces, shrink any disagreement to a minimal repro, and record a corpus:

```
lake build                                          # proofs, examples, oracle
lake test                                           # corpus and repros still match the model; no browser
node harness/run.cjs <target> [traces=300] [seed=1] [--results <file>]
node harness/run.cjs --record <corpus.json> [traces] [seed]   # also prints outcome coverage
```

`--results` writes the run as machine-readable results ([`results/README.md`](../results/README.md)).

## How implementations are compared

- Every call that returns a promise must return one. A synchronous throw is reported as `threw:` and doesn't count as a rejection.
- An exception matches only if it is a real `DOMException` (or `TypeError`) with the expected name.
- Each call has a 5-second timeout, so an implementation that never settles a promise shows up as `timeout` instead of hanging the run.
- The harness serves the frame tree from a local HTTP server, with origins 0, 1 and 2 as `http://127.0.0.1:<port A>`, `http://localhost:<port A>` and `http://127.0.0.1:<port B>` (loopback, so potentially trustworthy), and origin 3 as `https://other.example`, which no document has. Each operation runs in the document it names (`doc`), with registration signal `n` belonging to document `n / 3`. A `Tool` is printed with `@<document>` when its `source` is another document's window, and, for operations that name a document, with `!origin=<value>` when its `origin` isn't its source document's.
- Where the spec allows several outcomes, the expected outcome is `any:` followed by a JSON array of them, and any one matches. A `concurrent` operation's outcome is `all:` followed by a JSON array of its actions' outcomes, compared one by one. The oracle gives each operation the outcomes allowed from any state the earlier operations may have left, so it doesn't check that a later operation's outcome goes with the one an earlier operation actually had.
- A divergence listed in `expectations/<family>.json` (such as spec issue #361's result strings) is counted under its id and the trace goes on, so it doesn't hide other bugs later in the same trace (or, for one marked `stop` because it leaves the states apart, the trace ends without failing). Where the model allows several outcomes, an expectation may explain any one of them; a `concurrent` operation's actions are matched one by one. Any other divergence ends that trace, and makes the run exit non-zero. `--no-expectations` counts everything as unexpected.

## Expected divergences

[`expectations/`](../expectations) holds the known divergences per target family (#361, version lag, and polyfill bugs and a possible spec issue found with frames and calls in flight), each scoped to the versions it applies to. The format is in [`expectations/README.md`](../expectations/README.md).

## WPT export

The repros can be turned into WPT testharness.js tests and run in Playwright (see [`wpt-export/README.md`](../wpt-export/README.md)):

```
node tools/export-wpt.cjs repros/*.json --focus
node tools/run-wpt-export.cjs <wpt checkout> <target>
```
