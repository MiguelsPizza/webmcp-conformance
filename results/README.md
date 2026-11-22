# Generated results

Written by `node harness/run.cjs <target> ... --results results/<label>.json`. Each file records:

- `target`, `implementation` (for the polyfill: its path, `package.json` version, git commit and remote; for Chromium: the executable and version) and `browser` (`browser.version()` and the Playwright version)
- `spec`: the spec commit the model reflects, and `corpus`: the replayed file, or the seed and count of generated traces
- `date`, and `expectations`: the file used, which entries applied and which were skipped for this version
- `counts`: `calls` in all traces; `compared`, the calls up to and including each trace's first unexpected divergence; of those, how many `agree`, how many matched each `expected` id, and how many traces had an `unexpected` divergence
- `unexpected`: per kind of first unexpected divergence, how many traces hit it, and one trace with the model's and the implementation's outcome for each call: the shortest such trace cut after the divergence (replay), or the trace shrunk to a minimal one (live)

| File | Target | Run |
|---|---|---|
| [`polyfill-pr25-63ddbfd.json`](polyfill-pr25-63ddbfd.json) | polyfill PR #25 head | corpus replay |
| [`polyfill-pr25-63ddbfd-live.json`](polyfill-pr25-63ddbfd-live.json) | polyfill PR #25 head | 1,000 live traces, seed 1 |
| [`polyfill-main-4c01562.json`](polyfill-main-4c01562.json) | polyfill main | corpus replay |
| [`polyfill-main-4c01562-live.json`](polyfill-main-4c01562-live.json) | polyfill main | 1,000 live traces, seed 1 |
| [`chromium-157.0.8103.78.json`](chromium-157.0.8103.78.json) | Playwright 1.63.0's bundled Chromium | corpus replay |
| [`chromium-157.0.8103.78-live.json`](chromium-157.0.8103.78-live.json) | Playwright 1.63.0's bundled Chromium | 1,000 live traces, seed 1 |

`wpt-export-<label>.json` are runs of the exported WPT tests ([`../wpt-export/`](../wpt-export)) by `tools/run-wpt-export.cjs --json`, and `wpt-existing-361-<label>.json` the same runner on the three existing WPT tests that assert Chromium's side of #361.
