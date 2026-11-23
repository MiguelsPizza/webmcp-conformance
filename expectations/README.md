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

- `issue` or `spec`: the issue or pull request tracking it, or, for one nobody has filed yet, the spec section it departs from.
- `status`: `open-spec-question` (the spec may change, as with [#361](https://github.com/webmachinelearning/webmcp/issues/361)), `possible-spec-issue` (the implementation does what the spec may mean, but no issue is filed yet), `implementation-lag` (the implementation predates a spec change and a fix exists) or `implementation-bug` (the implementation disagrees with the current spec and no fix exists yet).
- `versions` (optional): the implementation versions it applies to, as `<`, `<=`, `>`, `>=` or `=` and a dotted version, compared with Chromium's `browser.version()` or the polyfill's `package.json` version.
- `match`: an outcome `got` for operation `op` (a name or a list), where the model says `want`, is this divergence when applying each rewrite to `want` in order, as `want.replace(new RegExp(from, flags), to)`, gives exactly `got`. Outcomes are in the corpus form (`corpus/README.md`). Instead of `rewrite`, `actual` (with an optional `want`) matches when want matches the regex `want` and got the regex `actual`, for an implementation that gives one of several outcomes in place of the spec's.
  - `where` (optional): fields the operation must have, such as `{"doc": 4}`.
  - `after` (optional): a list of field sets, each of which some earlier operation, or an action of an earlier `concurrent` operation, must have, such as `{"act": "cancel"}`.
  - Where the model allows several outcomes (`any:[...]`), got matches if it matches one of them. A `concurrent` operation's outcomes (`all:[...]`) are matched action by action, each as an operation of its action's kind (`act`) in the concurrent operation's document.

An expected divergence is counted under its id and the trace is compared on, as if the outcomes agreed. Any other divergence is unexpected: it ends that trace's comparison, and the run exits non-zero. So a run passes when the only differences are ones listed here, and a listed one that stops occurring shows up as a zero count.

Only divergences that leave the model and the implementation in the same state belong here as plain entries. For example, Chromium 157 accepting an `outputSchema` the spec rejects registers a tool the model doesn't have, so every later `getTools()` would differ too; it stays unexpected. A divergence that does leave the states apart can be listed with `"stop": true` when its conditions pin it down: it is counted under its id and ends that trace's comparison without failing the run, since what follows can't be compared.
