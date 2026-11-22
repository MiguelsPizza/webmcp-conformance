You are updating an executable Lean 4 model of the WebMCP spec so it matches a newer spec commit.
A person will review your change against the spec diff before it merges, so make it easy to check.

## The repository

- `WebMCP/Model.lean`: the model. Each definition cites the spec passage it transcribes as
  `Spec: #<anchor>` plus the step. Its header and `README.md` say what is in and out of scope.
- `spec/anchors.json`: the spec commit modelled, and for each spec passage the model transcribes,
  a marker string that locates it in `index.bs` and a hash of its text. The workflow refreshes the
  commit and hashes after you finish; you only edit it when a passage is added, removed, or its
  marker text changes. `tools/check-spec.cjs <index.bs>` reports which passages changed.
- `WebMCP/Proofs.lean`: machine-checked invariants of the model. It ends with
  `#guard_msgs in #print axioms` lines pinning each theorem to Lean's three standard axioms.
- `WebMCP/Examples.lean`: worked examples checked at build time.
- `Main.lean`: the oracle executable; parses JSON operations and prints the model's outcomes.
- `harness/run.cjs`: generates random call sequences, asks the oracle, and runs them in browsers.
- `corpus/spec-*.json`: recorded sequences and expected outcomes. Do not edit it; after you
  finish, the workflow re-records it from your model as `corpus/spec-<new commit>.json`, with the
  new commit as its `spec` value, and updates the corpus path in `README.md`.

## The spec change

`$SPEC_DIR` holds:

- `range.txt`: the spec commit currently modelled and the one to move to
- `log.txt`: the spec commits in between
- `index.bs.diff`: the diff of the spec source (`index.bs`) between them
- `index.bs`: the spec source at the new commit, for reading whole algorithms
- `anchors.txt`: the output of `tools/check-spec.cjs` against it: which modelled passages changed

## What to do

1. Read the diff and decide which changes affect behaviour the model covers (see the scope in
   `README.md` and the header of `Model.lean`). Editorial changes, explainer text, and algorithms
   outside the modelled slice need no model change.
2. For each change in scope, update `Model.lean` so it follows the new spec text step by step, and
   update the step citations. Transcribe; do not improve on the spec or guess at intent. If the
   new prose is ambiguous, model the most literal reading and say so in your summary.
3. Update the spec commit named in the header of `Model.lean` and in `README.md` (if they name
   one) to the new short commit. If the change adds a passage the model now transcribes, add it to
   `spec/anchors.json` (any hash; the workflow recomputes it) and cite it as `Spec: #<anchor>`.
4. If the model gains an operation, outcome, or input the harness has to generate or run, extend
   `Main.lean` and `harness/run.cjs` to match, keeping their existing style.
5. Run `lake build --wfail WebMCP oracle`. It must pass with no warnings, and the build lints
   for missing docstrings, so every new definition needs one. If you add a theorem, pin its
   axioms the same way as the others.
   - If a proof breaks, repair it. Never use `sorry`, `admit`, `axiom`, `native_decide`, or
     `set_option ... in` to get around a failure.
   - Do not weaken or delete a theorem to make it pass. If the spec change makes a proved property
     false, keep the theorem statement, leave the build failing, and explain which spec change
     breaks it and why. That is a finding the reviewer needs, not something to hide.
6. Run `.github/spec-update/check.sh` if you want to see the full gate; the corpus check in it is
   expected to fail until the workflow re-records the corpus.

Keep the change minimal: touch only what the spec change requires, and don't restructure,
reformat, or rename existing code. Don't touch `RESULTS.md`, the corpus, the hashes or commit in `spec/anchors.json`, or anything
under `.github/`.
You have no git or network access, and don't need it.

## What to write when you are done

Write two files in `$OUT_DIR`:

- `pr-title.txt`: one line, under 70 characters, saying what changed in the model, such as
  "Model executeTool cancellation from spec abc1234". If nothing in scope changed, use
  "Move the model to spec <short commit> (no model change)".
- `pr-body.md`: a short pull request description in the first person, as the repository owner
  would write it. No headings beyond what's needed, no inventories, no praise, no mention of
  being an AI or of any tool. Cover:
  - which spec commits (by PR number where the log has one) changed what, in a sentence each
  - what you changed in the model, citing the spec algorithm and step for each change
  - anything a reviewer must decide: ambiguous prose, a proof that no longer holds, or scope
    you left out on purpose
  Don't @-mention anyone. Don't describe build or check results; the workflow appends those.
