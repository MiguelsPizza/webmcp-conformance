/-!
# An executable model of the WebMCP spec

This file models one slice of the WebMCP spec, for a single document whose callers are all
same-origin:

* `registerTool()`: Web IDL conversion failures, the validation steps in spec order, schema
  serialization, and unregistration through the registration `signal`
* `getTools()`: every registered tool, sorted by name, with the members a `Tool` exposes
* `executeTool()`: lookup by tool id, input serialization, "invalid input", and how the
  callback's outcome becomes a result string or an error

Spec: <https://webmachinelearning.github.io/webmcp/> at upstream commit recorded in
`spec/anchors.json`. Every definition names the algorithm it models with a `Spec:` line giving
the algorithm's anchor in `index.bs`; `tools/check-spec.cjs` fails when the text of one of those
algorithms changes upstream, so the model cannot silently fall behind.

## Abstractions

The model is deliberately smaller than the spec. Each simplification below is either harmless
for this slice or listed as not covered in the README:

* Realms, tasks and events are not modelled. Calls are awaited one at a time, except
  `Op.registerAbortSync`, which aborts the signal before the registration promise settles.
* Author-supplied values are drawn from small enumerations (`Schema`, `Behavior`, `Input`,
  `Annotations`) whose JSON serializations are fixed. The harness builds the matching
  JavaScript values.
* Names are compared with `String` order. The spec orders by code units; the two agree on every
  name `validName` accepts, because those are ASCII.
-/
namespace WebMCP

/-- An exception name a caller can observe: the `TypeError`s thrown by Web IDL and by JSON
    serialization, and the `DOMException` names the spec rejects with.
    Spec: #tool-execution-error -/
inductive Err where
  /-- A `TypeError`. -/
  | typeError
  /-- An `"InvalidStateError"` `DOMException`. -/
  | invalidState
  /-- An `"AbortError"` `DOMException` (an aborted signal's default reason). -/
  | abort
  /-- A `"NotFoundError"` `DOMException` ("tool not found"). -/
  | notFound
  /-- A `"DataError"` `DOMException` ("invalid input"). -/
  | dataError
  /-- An `"OperationError"` `DOMException` ("tool rejected" or "unserializable result"). -/
  | operation
  deriving Repr, DecidableEq

/-- The exception's `name`, as the harness reports it. -/
def Err.name : Err → String
  | .typeError    => "TypeError"
  | .invalidState => "InvalidStateError"
  | .abort        => "AbortError"
  | .notFound     => "NotFoundError"
  | .dataError    => "DataError"
  | .operation    => "OperationError"

/-- An `inputSchema` or `outputSchema` member of a `ModelContextTool`. -/
inductive Schema where
  /-- The member is omitted. -/
  | absent
  /-- The object `{type: "object"}`. -/
  | object
  /-- An object whose `toJSON()` returns `{type: "string"}`. -/
  | viaToJSON
  /-- An object with a cycle: `JSON.stringify` throws a `TypeError`. -/
  | unserializable
  /-- The string `"x"`: converting it to the IDL `object` type throws a `TypeError`. -/
  | nonObject
  deriving Repr, DecidableEq

/-- The JSON a `Tool` exposes for a schema that registered successfully: "serialize a tool
    schema" followed by "parse a JSON string to a JavaScript value", or null when absent.
    Spec: #serialize-a-tool-schema -/
def Schema.exposed : Schema → String
  | .object    => "{\"type\":\"object\"}"
  | .viaToJSON => "{\"type\":\"string\"}"
  | _          => "null"

/-- A `ToolAnnotations` dictionary after conversion: every member defaults to false. -/
structure Annotations where
  /-- `readOnlyHint` -/
  readOnly : Bool := false
  /-- `untrustedContentHint` -/
  untrustedContent : Bool := false
  /-- `consequentialHint` -/
  consequential : Bool := false
  /-- `debugging` -/
  debugging : Bool := false
  deriving Repr, DecidableEq

/-- The `annotations` a `Tool` exposes, as JSON with members in IDL order, or null. -/
def Annotations.exposed : Option Annotations → String
  | none => "null"
  | some a =>
    "{\"readOnlyHint\":" ++ toString a.readOnly ++
    ",\"untrustedContentHint\":" ++ toString a.untrustedContent ++
    ",\"consequentialHint\":" ++ toString a.consequential ++
    ",\"debugging\":" ++ toString a.debugging ++ "}"

/-- What the author's `execute` callback does when invoked. -/
inductive Behavior where
  /-- Resolves with the input object it received. -/
  | echo
  /-- Resolves with `Object.keys(input)`, which shows whether the tool got a JSON copy. -/
  | keys
  /-- Returns a rejected promise. -/
  | reject
  /-- Throws synchronously; Web IDL turns that into a rejected promise. -/
  | throwSync
  /-- Resolves with `undefined`, which JSON cannot serialize. -/
  | returnUndefined
  /-- Resolves with the string `"hi"`. -/
  | returnText
  /-- Resolves with the empty string. -/
  | returnEmpty
  /-- Resolves with `null`. -/
  | returnNull
  /-- Resolves with the number `5`. -/
  | returnNumber
  /-- Resolves with an object with a cycle, which JSON cannot serialize. -/
  | returnCyclic
  deriving Repr, DecidableEq

/-- The `inputObject` a caller passes to `executeTool()`. -/
inductive Input where
  /-- The object `{n: <n>}`. -/
  | obj (n : Nat)
  /-- The argument is omitted, so the spec uses a new empty object. -/
  | omitted
  /-- `{n: <n>, f: <a function>}`: JSON drops `f`. -/
  | withFunction (n : Nat)
  /-- An object whose `toJSON()` returns `5`, so the JSON is not an object. -/
  | toJSONNumber
  /-- An object with a cycle, which JSON cannot serialize. -/
  | unserializable
  deriving Repr, DecidableEq

/-- "serializing a JavaScript value to a JSON string" given the input: `none` when it throws. -/
def Input.serialize : Input → Option String
  | .obj n          => some ("{\"n\":" ++ toString n ++ "}")
  | .omitted        => some "{}"
  | .withFunction n => some ("{\"n\":" ++ toString n ++ "}")
  | .toJSONNumber   => some "5"
  | .unserializable => none

/-- Whether parsing the serialized input gives an Object ("invoke the execute callback"). -/
def Input.parsesToObject : Input → Bool
  | .toJSONNumber => false
  | _             => true

/-- `Object.keys` of the object the tool receives, as JSON. -/
def Input.keysJSON : Input → String
  | .omitted => "[]"
  | _        => "[\"n\"]"

/-- The arguments to `registerTool()`, as JavaScript values before Web IDL conversion.
    Spec: #model-context-tool -/
structure ToolArgs where
  /-- `name` -/
  name : String
  /-- `title`, or `none` when omitted. -/
  title : Option String
  /-- `description`, or `none` when the required member is missing. -/
  description : Option String
  /-- `inputSchema` -/
  inputSchema : Schema
  /-- `outputSchema` -/
  outputSchema : Schema
  /-- `annotations`, or `none` when omitted. -/
  annotations : Option Annotations
  /-- What `execute` does. -/
  behavior : Behavior
  deriving Repr

/-- The spec's "tool definition" struct, trimmed to what this slice observes.
    Spec: #tool-definition -/
structure ToolDef where
  /-- "tool id": a unique internal value. -/
  id : Nat
  /-- "name" -/
  name : String
  /-- "title": null when the member was omitted. -/
  title : Option String
  /-- "description" -/
  description : String
  /-- "input schema" -/
  inputSchema : Schema
  /-- "output schema" -/
  outputSchema : Schema
  /-- "annotations" -/
  annotations : Option Annotations
  /-- What the tool's callback does ("execute steps"). -/
  behavior : Behavior
  /-- The registration signal whose abort steps unregister this tool. -/
  signal : Option Nat
  deriving Repr

/-- A `Tool` object returned by `getTools()`: the "tool id" it identifies and its name. -/
structure Handle where
  /-- `Tool`'s "tool id" -/
  id : Nat
  /-- `Tool`'s "name" -/
  name : String
  deriving Repr, DecidableEq

/-- The members of a `Tool` the harness compares, rendered as strings.
    Spec: #tool-interface -/
structure ToolView where
  /-- `name` -/
  name : String
  /-- `title` -/
  title : String
  /-- `description` -/
  description : String
  /-- `inputSchema`, as JSON -/
  inputSchema : String
  /-- `outputSchema`, as JSON -/
  outputSchema : String
  /-- `annotations`, as JSON -/
  annotations : String
  deriving Repr, DecidableEq

/-- The document's model context plus the caller's own state. -/
structure State where
  /-- Source of fresh "unique internal values" for tool ids. -/
  nextId : Nat := 0
  /-- The "tool map", in insertion order. -/
  tools : List ToolDef := []
  /-- The `AbortSignal`s that have fired. -/
  aborted : List Nat := []
  /-- The `Tool` objects each `getTools()` call returned, in order. -/
  handles : List (List Handle) := []
  deriving Repr

/-- One call the harness makes. -/
inductive Op where
  /-- `await registerTool(t, {signal})`. -/
  | register (t : ToolArgs) (signal : Option Nat)
  /-- `registerTool(t, {signal})`, then abort that signal before awaiting the promise. -/
  | registerAbortSync (t : ToolArgs) (signal : Nat)
  /-- Abort a registration signal. -/
  | abort (signal : Nat)
  /-- `await getTools()`. -/
  | getTools
  /-- `await executeTool(tool, input)` with the `index`-th `Tool` of the `call`-th `getTools()`. -/
  | execute (call index : Nat) (input : Input)
  deriving Repr

/-- What a call settles with. -/
inductive Outcome where
  /-- Fulfilled with undefined. -/
  | ok
  /-- Rejected with this exception. -/
  | err (e : Err)
  /-- `getTools()` fulfilled with these tools. -/
  | tools (ts : List ToolView)
  /-- `executeTool()` fulfilled with this string. -/
  | result (json : String)
  /-- The trace refers to a `Tool` no earlier `getTools()` returned. The harness never sends
      such a trace, and treats this outcome as its own bug. -/
  | invalidRequest
  deriving Repr, DecidableEq

/-- One `Tool` as the harness prints it: its members separated by `|`. -/
def ToolView.render (v : ToolView) : String :=
  "|".intercalate [v.name, v.title, v.description, v.inputSchema, v.outputSchema, v.annotations]

/-- An outcome as the harness prints it. -/
def Outcome.render : Outcome → String
  | .ok             => "ok"
  | .err e          => "err:" ++ e.name
  | .tools ts       => "tools:" ++ ";".intercalate (ts.map ToolView.render)
  | .result j       => "result:" ++ j
  | .invalidRequest => "invalid-request"

/-- A code point allowed in a tool name: ASCII alphanumeric, `_`, `-` or `.`. -/
def validNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.'

/-- The name rule from the "tool definition" struct and `registerTool()`: length 1 to 128 and
    only `validNameChar`s. `String.length` counts code points and the spec counts code units;
    they agree whenever every character passes `validNameChar`, and any other name is rejected
    either way. -/
def validName (n : String) : Bool :=
  0 < n.length && n.length ≤ 128 && n.all validNameChar

/-- Whether a tool named `n` is registered. -/
def hasName (s : State) (n : String) : Bool :=
  s.tools.any (·.name == n)

/-- The tool ids in the tool map. -/
def ids (s : State) : List Nat := s.tools.map (·.id)

/-- Whether converting the arguments to a `ModelContextTool` dictionary succeeds. Web IDL
    converts the dictionary before the method steps run, so any failure here is a `TypeError`
    that comes before every spec step. -/
def converts (t : ToolArgs) : Bool :=
  t.description.isSome && t.inputSchema != .nonObject && t.outputSchema != .nonObject

/-- The checks of `registerTool()`, in spec order. `none` means the tool is registered.
    Spec: #dom-modelcontext-registertool -/
def registerCheck (s : State) (t : ToolArgs) (sig : Option Nat) : Option Err :=
  -- Web IDL dictionary conversion.
  if !converts t then some .typeError
  -- "If tool map's values contains a tool definition whose name is tool name ..."
  else if hasName s t.name then some .invalidState
  -- "If either tool name is the empty string, or its length is greater than 128, or ..."
  else if !validName t.name then some .invalidState
  -- "If tool's description is the empty string ..."
  else if t.description == some "" then some .invalidState
  -- "serialize a tool schema" throws for the input schema, then for the output schema.
  else if t.inputSchema == .unserializable then some .typeError
  else if t.outputSchema == .unserializable then some .typeError
  -- "If options's signal exists and is aborted, reject with its abort reason."
  else if (sig.map s.aborted.contains).getD false then some .abort
  else none

/-- The tool definition `registerTool()` adds when every check passes. -/
def newTool (s : State) (t : ToolArgs) (sig : Option Nat) : ToolDef :=
  { id := s.nextId, name := t.name, title := t.title, description := t.description.getD "",
    inputSchema := t.inputSchema, outputSchema := t.outputSchema,
    annotations := t.annotations, behavior := t.behavior, signal := sig }

/-- Add the new tool definition to the tool map under a fresh tool id. -/
def insert (s : State) (t : ToolArgs) (sig : Option Nat) : State :=
  { s with nextId := s.nextId + 1, tools := s.tools ++ [newTool s t sig] }

/-- `registerTool()`, awaited. The document is fully active and allowed to use "tools".
    Spec: #dom-modelcontext-registertool -/
def register (s : State) (t : ToolArgs) (sig : Option Nat) : State × Outcome :=
  match registerCheck s t sig with
  | some e => (s, .err e)
  | none   => (insert s t sig, .ok)

/-- Aborting a registration signal runs "unregister a tool" for each tool it registered.
    A signal aborts at most once.
    Spec: #model-context-unregister-a-tool -/
def abort (s : State) (sig : Nat) : State × Outcome :=
  if s.aborted.contains sig then (s, .ok)
  else ({ s with aborted := sig :: s.aborted,
                 tools := s.tools.filter (·.signal != some sig) }, .ok)

/-- `registerTool()` followed by aborting its signal before the promise settles. If the tool
    was registered, the abort steps unregister it and reject the promise with the abort reason
    before the queued task can resolve it.
    Spec: #dom-modelcontext-registertool -/
def registerAbortSync (s : State) (t : ToolArgs) (sig : Nat) : State × Outcome :=
  let (s', o) := register s t (some sig)
  let (s'', _) := abort s' sig
  (s'', if o == .ok then .err .abort else o)

/-- The `Tool` view of a tool definition, as `getTools()` builds it. -/
def ToolDef.view (d : ToolDef) : ToolView :=
  { name := d.name, title := d.title.getD "", description := d.description,
    inputSchema := d.inputSchema.exposed, outputSchema := d.outputSchema.exposed,
    annotations := Annotations.exposed d.annotations }

/-- Sort by name. Names are ASCII (`validName`), so `String` order is the spec's
    "code unit less than". -/
def sortTools (l : List ToolDef) : List ToolDef :=
  l.mergeSort (fun a b => decide (a.name ≤ b.name))

/-- `getTools()`: every tool in the (single, same-origin) document, sorted by name.
    Spec: #dom-modelcontext-gettools -/
def getTools (s : State) : State × Outcome :=
  let found := sortTools s.tools
  ({ s with handles := s.handles ++ [found.map fun d => ⟨d.id, d.name⟩] },
   .tools (found.map ToolDef.view))

/-- The result of a callback that fulfilled, after "serializing a JavaScript value to a JSON
    string", or `none` when that throws ("unserializable result").
    Spec: #invoke-the-execute-callback -/
def callbackResult (b : Behavior) (input : Input) (json : String) : Option String :=
  match b with
  | .echo            => some json
  | .keys            => some input.keysJSON
  | .returnText      => some "\"hi\""
  | .returnEmpty     => some "\"\""
  | .returnNull      => some "null"
  | .returnNumber    => some "5"
  | .returnUndefined => none
  | .returnCyclic    => none
  | .reject          => none
  | .throwSync       => none

/-- What running a tool definition's execute steps settles with.
    Spec: #invoke-the-execute-callback -/
def runTool (d : ToolDef) (input : Input) (json : String) : Outcome :=
  -- "If inputObject is not an Object ... invalid input"
  if !input.parsesToObject then .err .dataError
  -- "tool rejected", and "unserializable result" for a fulfilled callback
  else match callbackResult d.behavior input json with
    | some r => .result r
    | none   => .err .operation

/-- `executeTool()`, "tool execute steps" and "invoke the execute callback". The in-parallel
    lookup in `executeTool()` and the one in "tool execute steps" are merged: with calls awaited
    one at a time, nothing can unregister the tool between them.
    Spec: #dom-modelcontext-executetool
    Spec: #tool-execute-steps -/
def execute (s : State) (call index : Nat) (input : Input) : State × Outcome :=
  match (s.handles[call]?).bind (·[index]?) with
  | none => (s, .invalidRequest)
  | some h =>
    -- "serializing a JavaScript value to a JSON string" given inputObject
    match input.serialize with
    | none => (s, .err .typeError)
    | some json =>
      -- "If targetToolMap[toolId] does not exist ... NotFoundError"
      match s.tools.find? (·.id == h.id) with
      | none   => (s, .err .notFound)
      | some d => (s, runTool d input json)

/-- One call. -/
def step (s : State) : Op → State × Outcome
  | .register t sig          => register s t sig
  | .registerAbortSync t sig => registerAbortSync s t sig
  | .abort sig               => abort s sig
  | .getTools                => getTools s
  | .execute c i input       => execute s c i input

/-- A sequence of calls, each awaited before the next. -/
def run (s : State) : List Op → State × List Outcome
  | [] => (s, [])
  | op :: ops =>
    let (s', o) := step s op
    let (s'', os) := run s' ops
    (s'', o :: os)

end WebMCP
