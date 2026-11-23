# Maintaining the model

## Browsable docs

The same docstrings, spec quotes and theorem statements as HTML pages, built with doc-gen4. The [Docs workflow](../.github/workflows/docs.yml) builds them on every push to main and attaches them to the run as the `docs` artifact. Locally (the first build compiles doc-gen4 and takes about 8 minutes; later ones take under a minute):

```
cd docbuild && DOCGEN_SRC=file lake build WebMCP:docs   # then open .lake/build/doc/WebMCP/Model.html
```

`DOCGEN_SRC=file` links each declaration to its local source file; leave it out to link to GitHub, which needs an `origin` remote on GitHub.

## Keeping it current

`node tools/check-spec.cjs <path to index.bs>` re-extracts each part of the spec the model transcribes and fails if its text changed since the commit in `spec/anchors.json`. For each changed part, update the definitions that cite it, then:

1. `lake build`. If a proved property no longer holds, the proof that stops compiling says which one.
2. `node tools/check-spec.cjs <index.bs> --update <sha>`.
3. Re-record the corpus, and refresh the repros' outcomes with `node tools/refresh-repros.cjs`.
4. Rerun the harness to see which implementations have caught up.

`bash .github/spec-update/check.sh` runs the whole gate the Check workflow runs: the build with no warnings, the proofs' axioms, the corpus against the model, and `lake test`. The [spec-update workflow](../.github/workflows/spec-update.yml) does the steps above for each new spec commit and opens a pull request; [`record-corpus.sh`](../.github/spec-update/record-corpus.sh) re-records the corpus and rewrites its path in the README.

The WPT score ([`wpt/README.md`](../wpt/README.md)) is pinned to one WPT and one spec commit: `node tools/wpt-score.cjs` fails if the model's answer to a translated subtest moves, but new or changed WPT files need translating by hand in [`wpt/translate.cjs`](../wpt/translate.cjs).
