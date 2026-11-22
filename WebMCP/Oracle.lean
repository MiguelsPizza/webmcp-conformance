import Lean.Data.Json
import WebMCP.Model

/-!
# The oracle's wire format

Parsing of the JSON operations the harness sends, and rendering of the outcomes it reads back.
`Main.lean` runs these over stdin. Malformed input is an error, never a default.
-/
namespace WebMCP.Oracle

open Lean

/-- A required member. -/
def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing member {k} in {j.compress}"

/-- A required member that may be null. -/
def nullable (j : Json) (k : String) : Except String (Option Json) := do
  let v ← field j k
  pure (if v.isNull then none else some v)

/-- Parse a schema member's wire value. -/
def parseSchema : String → Except String Schema
  | "absent" => pure .absent | "object" => pure .object | "viaToJSON" => pure .viaToJSON
  | "unserializable" => pure .unserializable | "nonObject" => pure .nonObject
  | s => throw s!"bad schema {s}"

/-- Parse a behavior's wire value. -/
def parseBehavior : String → Except String Behavior
  | "echo" => pure .echo | "keys" => pure .keys | "reject" => pure .reject
  | "throwSync" => pure .throwSync | "returnUndefined" => pure .returnUndefined
  | "returnText" => pure .returnText | "returnEmpty" => pure .returnEmpty
  | "returnNull" => pure .returnNull | "returnNumber" => pure .returnNumber
  | "returnCyclic" => pure .returnCyclic
  | s => throw s!"bad behavior {s}"

/-- Parse an input's wire value: `obj:<n>`, `fn:<n>`, `omitted`, `toJSONNumber` or `cyclic`. -/
def parseInput (s : String) : Except String Input :=
  match s.splitOn ":" with
  | ["obj", n] => (Input.obj ·) <$> (n.toNat?.elim (throw s!"bad input {s}") pure)
  | ["fn", n] => (Input.withFunction ·) <$> (n.toNat?.elim (throw s!"bad input {s}") pure)
  | ["omitted"] => pure .omitted
  | ["toJSONNumber"] => pure .toJSONNumber
  | ["cyclic"] => pure .unserializable
  | _ => throw s!"bad input {s}"

/-- Parse an annotations dictionary; omitted members take their IDL default, false. -/
def parseAnnotations (j : Json) : Except String Annotations := do
  let flag (k : String) : Except String Bool :=
    match j.getObjVal? k with
    | .ok v => v.getBool?
    | .error _ => pure false
  pure { readOnly := ← flag "readOnlyHint", untrustedContent := ← flag "untrustedContentHint",
         consequential := ← flag "consequentialHint", debugging := ← flag "debugging" }

/-- Parse the tool members of a register operation. -/
def parseTool (j : Json) : Except String ModelContextTool := do
  pure {
    name := ← (← field j "name").getStr?,
    title := ← (← nullable j "title").mapM (·.getStr?),
    description := ← (← nullable j "description").mapM (·.getStr?),
    inputSchema := ← parseSchema (← (← field j "inputSchema").getStr?),
    outputSchema := ← parseSchema (← (← field j "outputSchema").getStr?),
    annotations := ← (← nullable j "annotations").mapM parseAnnotations,
    behavior := ← parseBehavior (← (← field j "behavior").getStr?) }

/-- Parse one operation. -/
def parseOp (j : Json) : Except String Op := do
  match ← (← field j "op").getStr? with
  | "register" =>
    pure (.register (← parseTool j) (← (← nullable j "signal").mapM (·.getNat?)))
  | "registerAbortSync" =>
    pure (.registerAbortSync (← parseTool j) (← (← field j "signal").getNat?))
  | "abort" => pure (.abort (← (← field j "signal").getNat?))
  | "getTools" => pure .getTools
  | "execute" =>
    pure (.execute (← (← field j "call").getNat?) (← (← field j "index").getNat?)
      (← parseInput (← (← field j "input").getStr?)))
  | o => throw s!"bad op {o}"

/-- Parse one line: a JSON array of operations. -/
def parseLine (line : String) : Except String (List Op) := do
  let arr ← (← Json.parse line).getArr?
  arr.toList.mapM parseOp

/-- The outcomes of a line, as the JSON array of strings the harness reads. -/
def renderOutcomes (outcomes : List Outcome) : String :=
  (Json.arr (outcomes.map (Json.str ·.render)).toArray).compress

end WebMCP.Oracle
