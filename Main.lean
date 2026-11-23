import WebMCP.Oracle

/-!
# The oracle

Reads one JSON array of operations per line on stdin and prints, per line, the JSON array of
outcomes the model says the spec requires. Malformed input is an error, never a default.
The wire format is in `WebMCP/Oracle.lean`.
-/
open WebMCP

/-- Answer each line of operations with its outcomes until end of input. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    if line.trimAscii.isEmpty then continue
    let ops ← IO.ofExcept (Oracle.parseLine line)
    stdout.putStrLn (Oracle.renderOutcomes (explore [{}] ops))
    stdout.flush
