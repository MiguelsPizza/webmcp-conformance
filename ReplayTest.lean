import Lean.Data.Json

/-!
# `lake test`: replay recorded traces through the oracle

For every `*.json` in the directories (or files) given as arguments, in the corpus format
(`corpus/README.md`), feeds each trace's `ops` to the oracle built next to this executable and
fails if its outcomes differ from the trace's `want`. Needs no browser.
-/
open Lean

/-- The JSON files named by an argument: the file itself, or a directory's `*.json`, sorted. -/
def jsonFiles (arg : String) : IO (Array System.FilePath) := do
  let p : System.FilePath := arg
  if ← p.isDir then
    let entries ← p.readDir
    let files := entries.filter (·.path.extension == some "json") |>.map (·.path)
    pure (files.qsort (·.toString < ·.toString))
  else pure #[p]

/-- The traces of a corpus file, as `(ops, want)` pairs. -/
def traces (file : System.FilePath) : IO (Array (Json × Json)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let ts ← IO.ofExcept (j.getObjValAs? (Array Json) "traces")
  ts.mapM fun t => IO.ofExcept do pure ((← t.getObjVal? "ops"), (← t.getObjVal? "want"))

/-- Replay every trace through the oracle and report each file. -/
def main (args : List String) : IO UInt32 := do
  let oracle := (← IO.appPath).withFileName "oracle"
  let child ← IO.Process.spawn { cmd := oracle.toString, stdin := .piped, stdout := .piped }
  let mut failed := 0
  let mut total := 0
  for arg in args do
    for file in ← jsonFiles arg do
      let ts ← traces file
      let mut bad := 0
      for (ops, want) in ts do
        child.stdin.putStrLn ops.compress
        child.stdin.flush
        let got ← IO.ofExcept (Json.parse (← child.stdout.getLine))
        if got != want then
          bad := bad + 1
          if bad == 1 then
            IO.println s!"  {ops.compress}\n    want {want.compress}\n    got  {got.compress}"
      IO.println s!"{if bad == 0 then "ok  " else "FAIL"} {file}: {ts.size - bad} of {ts.size} traces match the model"
      failed := failed + bad
      total := total + ts.size
  let (_, child) ← child.takeStdin
  discard child.wait
  if total == 0 then
    IO.println "no traces found"
    return 1
  return if failed == 0 then 0 else 1
