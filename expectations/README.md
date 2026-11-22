# Expected divergences

`<family>.json` lists the divergences from the model that are known and tracked for one target family (`chromium`, `polyfill`). The harness loads the file for the target it runs, unless given `--expectations <file>` or `--no-expectations`.

```json
{
  "id": "361-string-result-not-json-encoded",
  "description": "What the implementation does instead, and why.",
  "issue": "https://github.com/webmachinelearning/webmcp/issues/361",
  "status": "open-spec-question",
  "versions": "<160",
  "match": { "op": "execute", "rewrite": [{ "from": "^result:\"(.+)\"$", "to": "result:$1" }] }
}
```

- `status`: `open-spec-question` (the spec may change, as with [#361](https://github.com/webmachinelearning/webmcp/issues/361)) or `implementation-lag` (the implementation predates a spec change and a fix exists).
- `versions` (optional): the implementation versions it applies to, as `<`, `<=`, `>`, `>=` or `=` and a dotted version, compared with Chromium's `browser.version()` or the polyfill's `package.json` version.
- `match`: an outcome `got` for operation `op` (a name or a list), where the model says `want`, is this divergence when applying each rewrite to `want` in order, as `want.replace(new RegExp(from, flags), to)`, gives exactly `got`. Outcomes are in the corpus form (`corpus/README.md`).

An expected divergence is counted under its id and the trace is compared on, as if the outcomes agreed. Any other divergence is unexpected: it ends that trace's comparison, and the run exits non-zero. So a run passes when the only differences are ones listed here, and a listed one that stops occurring shows up as a zero count.

Only divergences that leave the model and the implementation in the same state belong here. For example, Chromium 157 accepting an `outputSchema` the spec rejects registers a tool the model doesn't have, so every later `getTools()` would differ too; it stays unexpected.
