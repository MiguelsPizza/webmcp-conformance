/-
  An executable model of one slice of the WebMCP spec, for a single document whose
  callers are all same-origin:

  * registerTool()  validation order, abort-signal unregistration
  * getTools()      returns the registered tools sorted by name
  * executeTool()   tool lookup by tool id, result serialization, and the platform error outcomes

  Spec: https://webmachinelearning.github.io/webmcp/ at upstream commit 14b6d53.
  Each definition cites the algorithm step it models. Values the harness cannot observe
  (realms, tasks, events) are left out on purpose.
-/
namespace WebMCP

/-- The DOMException / TypeError names a caller can observe. -/
inductive Err where
  | typeError | invalidState | abort | notFound | operation
  deriving Repr, DecidableEq

def Err.name : Err → String
  | .typeError    => "TypeError"
  | .invalidState => "InvalidStateError"
  | .abort        => "AbortError"
  | .notFound     => "NotFoundError"
  | .operation    => "OperationError"

/-- How an `inputSchema` / `outputSchema` member behaves under "serialize a tool schema". -/
inductive Schema where
  | absent | ok | unserializable
  deriving Repr, DecidableEq

/-- What the author's `execute` callback does when invoked. -/
inductive Behavior where
  | echo            -- resolves with its input object
  | reject          -- returns a rejected promise
  | throwSync       -- throws synchronously (Web IDL turns this into a rejection)
  | returnUndefined -- resolves with undefined, which JSON cannot serialize
  | returnText      -- resolves with the string "hi"
  | returnEmpty     -- resolves with the empty string
  deriving Repr, DecidableEq

/-- The argument a caller passes to `executeTool()`. -/
inductive Input where
  | obj (n : Nat)     -- the object `{n: <n>}`
  | unserializable    -- an object with a cycle
  deriving Repr, DecidableEq

structure ToolArgs where
  name : String
  description : String
  inputSchema : Schema
  outputSchema : Schema
  behavior : Behavior
  deriving Repr

/-- The spec's "tool definition" struct, trimmed to what this slice observes. -/
structure ToolDef where
  id : Nat                 -- "tool id": a unique internal value
  name : String
  description : String
  behavior : Behavior
  signal : Option Nat      -- the registration signal whose abort steps unregister it
  deriving Repr

structure State where
  nextId : Nat := 0
  tools : List ToolDef := []                    -- the "tool map", in insertion order
  aborted : List Nat := []                      -- AbortSignals that have fired
  handles : List (List (Nat × String)) := []    -- Tool objects each getTools() returned
  deriving Repr

inductive Op where
  | register (t : ToolArgs) (signal : Option Nat)
  | abort (signal : Nat)
  | getTools
  /-- Execute the `index`-th Tool returned by the `call`-th getTools(). -/
  | execute (call index : Nat) (input : Input)
  deriving Repr

inductive Outcome where
  | ok
  | err (e : Err)
  | tools (names : List String)
  | result (json : String)
  deriving Repr, DecidableEq

def Outcome.render : Outcome → String
  | .ok        => "ok"
  | .err e     => "err:" ++ e.name
  | .tools ns  => "tools:" ++ ",".intercalate ns
  | .result j  => "result:" ++ j

/-- Tool name rule from the "tool definition" struct: length 1..128, ASCII alphanumeric, `_`, `-`, `.`.
    `String.length` counts code points while the spec counts code units; they agree on every
    string that passes the character check, and every other string is rejected either way. -/
def validNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.'

def validName (n : String) : Bool :=
  0 < n.length && n.length ≤ 128 && n.all validNameChar

def hasName (s : State) (n : String) : Bool :=
  s.tools.any (·.name == n)

def ids (s : State) : List Nat := s.tools.map (·.id)

/-- registerTool() method steps. The document is fully active and allowed to use "tools". -/
def register (s : State) (t : ToolArgs) (sig : Option Nat) : State × Outcome :=
  -- "If tool map's values contains a tool definition whose name is tool name ..."
  if hasName s t.name then (s, .err .invalidState)
  -- name length / code point check
  else if !validName t.name then (s, .err .invalidState)
  -- "If tool's description is the empty string ..."
  else if t.description == "" then (s, .err .invalidState)
  -- "serialize a tool schema": JSON.stringify throws, or yields undefined → TypeError
  else if t.inputSchema == .unserializable then (s, .err .typeError)
  else if t.outputSchema == .unserializable then (s, .err .typeError)
  -- "If options's signal exists and is aborted, reject with its abort reason"
  else if (sig.map s.aborted.contains).getD false then (s, .err .abort)
  else
    let d : ToolDef :=
      { id := s.nextId, name := t.name, description := t.description,
        behavior := t.behavior, signal := sig }
    ({ s with nextId := s.nextId + 1, tools := s.tools ++ [d] }, .ok)

/-- Aborting a registration signal runs "unregister a tool" for each tool it registered.
    A signal aborts at most once. -/
def abort (s : State) (sig : Nat) : State × Outcome :=
  if s.aborted.contains sig then (s, .ok)
  else ({ s with aborted := sig :: s.aborted,
                 tools := s.tools.filter (·.signal != some sig) }, .ok)

/-- getTools(): every tool in the (single, same-origin) document, sorted by name.
    Names are ASCII, so `String` order equals the spec's "code unit less than". -/
def sortTools (l : List (Nat × String)) : List (Nat × String) :=
  l.mergeSort (fun a b => decide (a.2 ≤ b.2))

def getTools (s : State) : State × Outcome :=
  let found := sortTools (s.tools.map fun d => (d.id, d.name))
  ({ s with handles := s.handles ++ [found] }, .tools (found.map (·.2)))

/-- executeTool(), "tool execute steps" and "invoke the execute callback". -/
def execute (s : State) (call index : Nat) (input : Input) : State × Outcome :=
  match input with
  -- "serializing a JavaScript value to a JSON string" given inputObject throws
  | .unserializable => (s, .err .typeError)
  | .obj n =>
    match (s.handles[call]?).bind (·[index]?) with
    | none => (s, .ok)  -- the harness never asks for a Tool it was not given
    | some (toolId, _) =>
      -- "If targetToolMap[toolId] does not exist ... NotFoundError"
      match s.tools.find? (·.id == toolId) with
      | none => (s, .err .notFound)
      | some d =>
        match d.behavior with
        | .echo            => (s, .result ("{\"n\":" ++ toString n ++ "}"))
        | .reject          => (s, .err .operation)  -- tool rejected
        | .throwSync       => (s, .err .operation)  -- tool rejected
        | .returnUndefined => (s, .err .operation)  -- unserializable result
        -- A string result is serialized to JSON like any other value, so it comes back quoted.
        | .returnText      => (s, .result "\"hi\"")
        | .returnEmpty     => (s, .result "\"\"")

def step (s : State) : Op → State × Outcome
  | .register t sig     => register s t sig
  | .abort sig          => abort s sig
  | .getTools           => getTools s
  | .execute c i input  => execute s c i input

def run (s : State) : List Op → State × List Outcome
  | [] => (s, [])
  | op :: ops =>
    let (s', o) := step s op
    let (s'', os) := run s' ops
    (s'', o :: os)

end WebMCP
