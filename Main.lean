import Lean.Data.Json
import WebMCP.Model

/-! Oracle: reads one JSON array of operations per line on stdin and prints, per line, the
    JSON array of outcomes the model says the spec requires. -/
open Lean WebMCP

def parseSchema : String → Except String Schema
  | "absent" => pure .absent | "ok" => pure .ok | "unserializable" => pure .unserializable
  | s => throw s!"bad schema {s}"

def parseBehavior : String → Except String Behavior
  | "echo" => pure .echo | "reject" => pure .reject
  | "throwSync" => pure .throwSync | "returnUndefined" => pure .returnUndefined
  | "returnText" => pure .returnText | "returnEmpty" => pure .returnEmpty
  | s => throw s!"bad behavior {s}"

def parseOp (j : Json) : Except String Op := do
  match ← j.getObjValAs? String "op" with
  | "register" =>
    let t : ToolArgs := {
      name := ← j.getObjValAs? String "name",
      description := ← j.getObjValAs? String "description",
      inputSchema := ← parseSchema (← j.getObjValAs? String "inputSchema"),
      outputSchema := ← parseSchema (← j.getObjValAs? String "outputSchema"),
      behavior := ← parseBehavior (← j.getObjValAs? String "behavior") }
    pure (.register t (j.getObjValAs? Nat "signal").toOption)
  | "abort" => pure (.abort (← j.getObjValAs? Nat "signal"))
  | "getTools" => pure .getTools
  | "execute" =>
    let input := match j.getObjValAs? Nat "input" with
      | .ok n => Input.obj n
      | .error _ => Input.unserializable
    pure (.execute (← j.getObjValAs? Nat "call") (← j.getObjValAs? Nat "index") input)
  | o => throw s!"bad op {o}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  if line.trim.isEmpty then loop stdin stdout
  let ops ← IO.ofExcept do
    let j ← Json.parse line
    let arr ← j.getArr?
    arr.toList.mapM parseOp
  let (_, outcomes) := run {} ops
  stdout.putStrLn (Json.arr (outcomes.map (Json.str ·.render)).toArray).compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
