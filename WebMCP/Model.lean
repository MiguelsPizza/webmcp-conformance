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
* `toJSON()` on a schema runs no page script here, so it can't register a tool or detach the
  document. The second duplicate-name check and the second "fully active" check that
  `registerTool()` makes after serializing the schemas therefore can't fail, and are omitted.
* The document is always fully active and allowed to use "tools", so those checks never fail.

## Spec terms and their Lean names

| Spec | Lean |
|---|---|
| `ModelContextTool` dictionary (the `registerTool()` argument) | `ModelContextTool` |
| tool definition (a value in the tool map) | `ToolDef` |
| tool id | `ToolDef.id`, `ToolObject.id` |
| `Tool` object returned by `getTools()` | `ToolObject` (what the caller holds), `ToolView` (what it exposes) |
| model context (its tool map) | `State` (`State.tools`) |
| `registerTool()` | `registerTool`; its validation steps are `registerToolChecks` |
| the abort steps `registerTool()` adds to its `signal` | `ToolDef.signal`, `State.abortSteps` |
| unregister a tool (run by those abort steps) | `unregisterBySignal` |
| `getTools()` | `getTools` |
| `executeTool()` | `executeTool` |
| tool execute steps | `toolExecuteSteps` |
| invoke the execute callback | `invokeExecuteCallback`, `callbackResult` |
| tool execution error, its corresponding exception name | `ToolExecutionError`, `ToolExecutionError.exceptionName` |
| `executeTool()`'s `completionSteps` | `completionOutcome` |

`Tool` alone is not used as a Lean name: the spec's `Tool` object is split here into the
`ToolObject` a caller holds and the `ToolView` it exposes, and a bare `Tool` would read as either,
or as the `ModelContextTool` dictionary.
-/
namespace WebMCP

/-- An exception a caller can observe: the `TypeError`s thrown by Web IDL and by JSON
    serialization, and the `DOMException` names the spec rejects with. Failures of a tool's
    execution reach the caller only as one of these, through
    `ToolExecutionError.exceptionName`. -/
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

/-- A "tool execution error": why a tool execution failed. "target document unloaded" is left
    out, since the model has one document and it never unloads. -/
inductive ToolExecutionError where
  /-- "tool not found": the tool is not registered in the target document. -/
  | toolNotFound
  /-- "invalid input": the input arguments could not be parsed into a JavaScript Object. -/
  | invalidInput
  /-- "tool rejected": the `execute` callback returned a rejected promise. -/
  | toolRejected
  /-- "unserializable result": the tool's result could not be serialized to a JSON string. -/
  | unserializableResult
  deriving Repr, DecidableEq

/-- A tool execution error's "corresponding exception name", row by row from the spec's table.
    Spec: #tool-execution-error -/
def ToolExecutionError.exceptionName : ToolExecutionError → Err
  | .toolNotFound         => .notFound
  | .invalidInput         => .dataError
  | .toolRejected         => .operation
  | .unserializableResult => .operation

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
structure ModelContextTool where
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
  /-- The registration signal whose abort steps unregister this tool. The spec keeps this on
      the signal's abort steps instead; the model only needs to know which signal it was. -/
  signal : Option Nat
  deriving Repr

/-- A `Tool` object returned by `getTools()`: the "tool id" it identifies and its name. -/
structure ToolObject where
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
  toolObjects : List (List ToolObject) := []
  /-- The "unregister a tool" abort steps `registerTool()` added, as (signal, tool id) pairs in
      the order they were added. The model never reads this: unregistering goes by
      `ToolDef.signal`. It is kept so that `Proofs.lean` can state the spec's `Assert` in
      "unregister a tool" about the steps the spec actually runs. -/
  abortSteps : List (Nat × Nat) := []
  deriving Repr

/-- One call the harness makes. -/
inductive Op where
  /-- `await registerTool(t, {signal})`. -/
  | register (t : ModelContextTool) (signal : Option Nat)
  /-- `registerTool(t, {signal})`, then abort that signal before awaiting the promise. -/
  | registerAbortSync (t : ModelContextTool) (signal : Nat)
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
def converts (t : ModelContextTool) : Bool :=
  t.description.isSome && t.inputSchema != .nonObject && t.outputSchema != .nonObject

/-- The checks of `registerTool()`, in spec order. `none` means the tool is registered.
    Spec: #dom-modelcontext-registertool -/
def registerToolChecks (s : State) (t : ModelContextTool) (sig : Option Nat) : Option Err :=
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
  -- (`sig` is given and has already been aborted.)
  else if (sig.map s.aborted.contains).getD false then some .abort
  else none

/-- The tool definition `registerTool()` adds when every check passes. -/
def newTool (s : State) (t : ModelContextTool) (sig : Option Nat) : ToolDef :=
  { id := s.nextId, name := t.name, title := t.title, description := t.description.getD "",
    inputSchema := t.inputSchema, outputSchema := t.outputSchema,
    annotations := t.annotations, behavior := t.behavior, signal := sig }

/-- Add the new tool definition to the tool map under a fresh tool id, and, when a signal was
    given, the abort steps that unregister it. -/
def addTool (s : State) (t : ModelContextTool) (sig : Option Nat) : State :=
  { s with nextId := s.nextId + 1, tools := s.tools ++ [newTool s t sig],
           abortSteps := match sig with
             | some g => s.abortSteps ++ [(g, s.nextId)]
             | none   => s.abortSteps }

/-- `registerTool()`, awaited. The document is fully active and allowed to use "tools".
    Spec: #dom-modelcontext-registertool -/
def registerTool (s : State) (t : ModelContextTool) (sig : Option Nat) : State × Outcome :=
  match registerToolChecks s t sig with
  | some e => (s, .err e)
  | none   => (addTool s t sig, .ok)

/-- Aborting a registration signal runs its abort steps: "unregister a tool" for each tool it
    registered. A signal aborts at most once.
    Spec: #model-context-unregister-a-tool -/
def unregisterBySignal (s : State) (sig : Nat) : State × Outcome :=
  if s.aborted.contains sig then (s, .ok)
  else ({ s with aborted := sig :: s.aborted,
                 tools := s.tools.filter (·.signal != some sig) }, .ok)

/-- `registerTool()` followed by aborting its signal before the promise settles. If the tool
    was registered, the abort steps unregister it and reject the promise with the abort reason
    before the queued task can resolve it.
    Spec: #dom-modelcontext-registertool -/
def registerAbortSync (s : State) (t : ModelContextTool) (sig : Nat) : State × Outcome :=
  let (s', o) := registerTool s t (some sig)
  let (s'', _) := unregisterBySignal s' sig
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
  ({ s with toolObjects := s.toolObjects ++ [found.map fun d => ⟨d.id, d.name⟩] },
   .tools (found.map ToolDef.view))

/-- How the author's callback settles, after "serializing a JavaScript value to a JSON string"
    for a fulfilled one: the result string, "unserializable result" when that throws, or
    "tool rejected".
    Spec: #invoke-the-execute-callback -/
def callbackResult (b : Behavior) (input : Input) (json : String) :
    Except ToolExecutionError String :=
  match b with
  -- "If toolPromise was fulfilled with value v": serialize v.
  | .echo            => .ok json
  | .keys            => .ok input.keysJSON
  | .returnText      => .ok "\"hi\""
  | .returnEmpty     => .ok "\"\""
  | .returnNull      => .ok "null"
  | .returnNumber    => .ok "5"
  -- "If this throws an exception, run completionSteps given null and unserializable result"
  | .returnUndefined => .error .unserializableResult
  | .returnCyclic    => .error .unserializableResult
  -- "If toolPromise was rejected with reason r": "tool rejected"
  | .reject          => .error .toolRejected
  | .throwSync       => .error .toolRejected

/-- Run a tool definition's execute steps ("invoke the execute callback"): parse the input, then
    run the author's callback.
    Spec: #invoke-the-execute-callback -/
def invokeExecuteCallback (d : ToolDef) (input : Input) (json : String) :
    Except ToolExecutionError String :=
  -- "If inputObject is not an Object, then run completionSteps given null and invalid input"
  if !input.parsesToObject then .error .invalidInput
  else callbackResult d.behavior input json

/-- "tool execute steps": look the tool up by its tool id, then run its execute steps.
    Spec: #tool-execute-steps -/
def toolExecuteSteps (s : State) (toolId : Nat) (input : Input) (json : String) :
    Except ToolExecutionError String :=
  -- "If toolMap[toolId] does not exist, then run completionSteps given null and tool not found"
  match s.tools.find? (·.id == toolId) with
  | none   => .error .toolNotFound
  | some d => invokeExecuteCallback d input json

/-- `executeTool()`'s `completionSteps`: resolve with the result, or reject with a
    `DOMException` whose name is the error's "corresponding exception name".
    Spec: #dom-modelcontext-executetool -/
def completionOutcome : Except ToolExecutionError String → Outcome
  | .ok r    => .result r
  | .error e => .err e.exceptionName

/-- `executeTool()`. Its in-parallel lookup of the tool id and the one in "tool execute steps"
    are merged into `toolExecuteSteps`: with calls awaited one at a time, nothing can unregister
    the tool between them, and both reject with `NotFoundError`.
    Spec: #dom-modelcontext-executetool -/
def executeTool (s : State) (call index : Nat) (input : Input) : State × Outcome :=
  match (s.toolObjects[call]?).bind (·[index]?) with
  | none => (s, .invalidRequest)
  | some tool =>
    -- "serializing a JavaScript value to a JSON string" given inputObject
    match input.serialize with
    | none => (s, .err .typeError)
    | some json => (s, completionOutcome (toolExecuteSteps s tool.id input json))

/-- One call. -/
def step (s : State) : Op → State × Outcome
  | .register t sig          => registerTool s t sig
  | .registerAbortSync t sig => registerAbortSync s t sig
  | .abort sig               => unregisterBySignal s sig
  | .getTools                => getTools s
  | .execute c i input       => executeTool s c i input

/-- A sequence of calls, each awaited before the next. -/
def run (s : State) : List Op → State × List Outcome
  | [] => (s, [])
  | op :: ops =>
    let (s', o) := step s op
    let (s'', os) := run s' ops
    (s'', o :: os)

end WebMCP
