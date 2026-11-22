/-!
# An executable model of the WebMCP spec

This file models one slice of the WebMCP spec, for a fixed frame tree of documents on several
origins (`harnessDocs`):

* `registerTool()`: Web IDL conversion failures, the validation steps in spec order, schema
  serialization, `exposedTo`, and unregistration through the registration `signal`
* `getTools()`: `fromOrigins`, which documents' tools are discovered and which of those are
  exposed to the caller, sorted by name, with the members a `Tool` exposes
* `executeTool()`: lookup by tool id in the `Tool`'s source document, the exposure check, input
  serialization, "invalid input", and how the callback's outcome becomes a result string or an
  error

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
* Documents are abstract: a fixed list (`harnessDocs`) in tree order, each with an origin (a
  number; equal numbers are same origin, and none is opaque) and whether it is allowed to use
  "tools", which stands in for permissions policy. Every document is fully active, in the same
  traversable navigable, and never navigates or unloads, so the "fully active", traversable and
  opaque-origin checks never fail and "target document unloaded" never happens. Each document's
  tool map is the part of `State.tools` tagged with its index.
* `exposedTo` and `fromOrigins` entries are drawn from `OriginArg`: an origin's serialization, a
  URL with a path, a string the URL parser rejects, and a URL that isn't potentially trustworthy.
* A `Tool` can be passed to `executeTool()` in any document. In a browser only a document that
  can reach the `Tool` object (the one that discovered it, or one same origin with it) can do so;
  the harness only generates those.

## Spec terms and their Lean names

| Spec | Lean |
|---|---|
| `ModelContextTool` dictionary (the `registerTool()` argument) | `ModelContextTool` |
| tool definition (a value in the tool map) | `ToolDef` |
| tool id | `ToolDef.id`, `ToolObject.id` |
| `Tool` object returned by `getTools()` | `ToolObject` (what the caller holds), `ToolView` (what it exposes) |
| model context (its tool map) | `State` (`State.tools`, per document by `ToolDef.doc`) |
| document, its origin, allowed to use "tools" | an index into `State.docs`, `docOrigin`, `docAllowed` |
| tool is exposed to an origin | `toolIsExposed` |
| exposed origins, `exposedTo`, `fromOrigins` | `ToolDef.exposedOrigins`, `OriginArg`, `parseOrigins` |
| toolOwnerIsRequested, the loop over navigables in `getTools()` | `requested`, `discover` |
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
  /-- A `"NotAllowedError"` `DOMException`: the document is not allowed to use "tools". -/
  | notAllowed
  /-- A `"SecurityError"` `DOMException`: an `exposedTo` or `fromOrigins` entry is not a
      potentially trustworthy origin. -/
  | security
  deriving Repr, DecidableEq

/-- A "tool execution error": why a tool execution failed. "target document unloaded" is left
    out, since documents never unload in the model. -/
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
  | .notAllowed   => "NotAllowedError"
  | .security     => "SecurityError"

/-- An origin. The model never looks inside one: two origins are same origin exactly when they
    are equal, and none is opaque. The harness maps each to a real origin (see the README). -/
abbrev Origin := Nat

/-- A document in the frame tree: its origin, and whether it is allowed to use the "tools"
    feature. -/
structure Doc where
  /-- The document's origin. -/
  origin : Origin
  /-- Whether the document is allowed to use the "tools" policy-controlled feature. -/
  allowed : Bool
  deriving Repr, DecidableEq

/-- The frame tree the harness serves, in tree order, which is the order of the top-level
    document's "inclusive descendant navigables". The index of a document in this list is how
    operations name it.

    0. the top-level document, origin 0
    1. an `<iframe>` in 0, origin 0
    2. an `<iframe allow="tools">` in 1, origin 2
    3. an `<iframe allow="tools">` in 0, origin 1
    4. an `<iframe>` in 0, origin 1, so not allowed to use "tools"

    The "tools" feature's default allowlist is `'self'`, so a cross-origin frame is allowed to
    use it only when its `<iframe>` delegates it with `allow="tools"`. Origin 3 belongs to no
    document.
    Spec: #permissions-policy -/
def harnessDocs : List Doc :=
  [⟨0, true⟩, ⟨0, true⟩, ⟨2, true⟩, ⟨1, true⟩, ⟨1, false⟩]

/-- A string in `exposedTo` or `fromOrigins`, before the URL parser runs. -/
inductive OriginArg where
  /-- The serialization of this origin. -/
  | origin (o : Origin)
  /-- A URL with this origin and a path and query, so it is not an origin's serialization. -/
  | withPath (o : Origin)
  /-- A string the URL parser fails on. -/
  | invalid
  /-- A URL whose origin is not potentially trustworthy (`http:` on a public host). -/
  | insecure
  deriving Repr, DecidableEq

/-- "Let parsedURL be the result of running the URL parser on origin. If parsedURL is failure
    or its origin is not potentially trustworthy, then return a promise rejected with a
    "SecurityError" DOMException": the origin, or `none` for that rejection. -/
def OriginArg.parse : OriginArg → Option Origin
  | .origin o   => some o
  | .withPath o => some o
  | .invalid    => none
  | .insecure   => none

/-- The loop `registerTool()` runs over `exposedTo` and `getTools()` over `fromOrigins`: the
    parsed origins in order, or `none` when one of them is rejected with a `SecurityError`.
    Spec: #model-context-register-tool-options
    Spec: #model-context-get-tool-options -/
def parseOrigins (l : List OriginArg) : Option (List Origin) :=
  l.mapM OriginArg.parse

/-- "tool is exposed to an origin": the tool owner's own origin, and every origin in its
    exposed origins, may see it.
    Spec: #tool-is-exposed-to-an-origin -/
def toolIsExposed (owner : Origin) (exposed : List Origin) (accessing : Origin) : Bool :=
  -- "If tool owner origin is same origin with accessing origin, then return true."
  owner == accessing ||
  -- "For each allowed origin of exposed origins: If accessing origin is same origin with
  -- allowed origin, then return true."
  exposed.any (· == accessing)

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
  /-- The document whose tool map holds this definition (the tool owner). The spec keeps one
      tool map per document; the model keeps them all in `State.tools`, tagged with this. -/
  doc : Nat
  /-- "exposed origins" -/
  exposedOrigins : List Origin
  deriving Repr

/-- A `Tool` object returned by `getTools()`: the "tool id" it identifies, its name, the
    document it came from and that document's origin. -/
structure ToolObject where
  /-- `Tool`'s "tool id" -/
  id : Nat
  /-- `Tool`'s "name" -/
  name : String
  /-- `Tool`'s "source": the window of this document. -/
  source : Nat
  /-- `Tool`'s "origin" -/
  origin : Origin
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
  /-- `source`, as the index of its document, or `none` when it is the caller's own window. The
      harness checks that `origin` is that document's origin. -/
  source : Option Nat
  deriving Repr, DecidableEq

/-- Every document's model context, plus the callers' own state. -/
structure State where
  /-- The frame tree, in tree order. No operation changes it. -/
  docs : List Doc := harnessDocs
  /-- Source of fresh "unique internal values" for tool ids. -/
  nextId : Nat := 0
  /-- Every document's "tool map", in insertion order. A definition's `doc` says whose. -/
  tools : List ToolDef := []
  /-- The `AbortSignal`s that have fired. -/
  aborted : List Nat := []
  /-- The `Tool` objects each `getTools()` call returned, in order (none for a rejected call). -/
  toolObjects : List (List ToolObject) := []
  /-- The "unregister a tool" abort steps `registerTool()` added, as (signal, tool id) pairs in
      the order they were added. The model never reads this: unregistering goes by
      `ToolDef.signal`. It is kept so that `Proofs.lean` can state the spec's `Assert` in
      "unregister a tool" about the steps the spec actually runs. -/
  abortSteps : List (Nat × Nat) := []
  deriving Repr

/-- One call the harness makes, in document `doc` (0, the top-level document, when not given). -/
inductive Op where
  /-- `await registerTool(t, {signal, exposedTo})`. -/
  | register (t : ModelContextTool) (signal : Option Nat) (exposedTo : List OriginArg := [])
      (doc : Nat := 0)
  /-- `registerTool(t, {signal, exposedTo})`, then abort that signal before awaiting the
      promise. -/
  | registerAbortSync (t : ModelContextTool) (signal : Nat) (exposedTo : List OriginArg := [])
      (doc : Nat := 0)
  /-- Abort a registration signal. -/
  | abort (signal : Nat)
  /-- `await getTools({fromOrigins})`. -/
  | getTools (fromOrigins : List OriginArg := []) (doc : Nat := 0)
  /-- `await executeTool(tool, input)` with the `index`-th `Tool` of the `call`-th `getTools()`,
      whichever document made that call. -/
  | execute (call index : Nat) (input : Input) (doc : Nat := 0)
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

/-- One `Tool` as the harness prints it: its members separated by `|`, then `@<document>` when
    its `source` is not the caller's own window. -/
def ToolView.render (v : ToolView) : String :=
  "|".intercalate [v.name, v.title, v.description, v.inputSchema, v.outputSchema, v.annotations] ++
  match v.source with
  | some d => "@" ++ toString d
  | none   => ""

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

/-- Whether document `doc` is allowed to use the "tools" feature. A document the frame tree
    doesn't have is not. -/
def docAllowed (s : State) (doc : Nat) : Bool :=
  (s.docs[doc]?.map (·.allowed)).getD false

/-- Document `doc`'s origin. -/
def docOrigin (s : State) (doc : Nat) : Origin :=
  (s.docs[doc]?.map (·.origin)).getD 0

/-- Whether document `doc`'s tool map has a tool named `n`. -/
def hasName (s : State) (doc : Nat) (n : String) : Bool :=
  s.tools.any (fun d => d.doc == doc && d.name == n)

/-- The tool ids in the tool map. -/
def ids (s : State) : List Nat := s.tools.map (·.id)

/-- Whether converting the arguments to a `ModelContextTool` dictionary succeeds. Web IDL
    converts the dictionary before the method steps run, so any failure here is a `TypeError`
    that comes before every spec step. -/
def converts (t : ModelContextTool) : Bool :=
  t.description.isSome && t.inputSchema != .nonObject && t.outputSchema != .nonObject

/-- The checks of `registerTool()` in document `doc`, in spec order. `none` means the tool is
    registered.
    Spec: #dom-modelcontext-registertool -/
def registerToolChecks (s : State) (t : ModelContextTool) (sig : Option Nat)
    (exp : List OriginArg) (doc : Nat) : Option Err :=
  -- Web IDL dictionary conversion.
  if !converts t then some .typeError
  -- "If tool owner is not allowed to use the "tools" feature, then return a promise rejected
  -- with a "NotAllowedError" DOMException."
  else if !docAllowed s doc then some .notAllowed
  -- "If tool map's values contains a tool definition whose name is tool name ..."
  else if hasName s doc t.name then some .invalidState
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
  -- "For each origin of options's exposedTo: ... If parsedURL is failure or its origin is not
  -- potentially trustworthy, then return a promise rejected with a "SecurityError"
  -- DOMException."
  else if (parseOrigins exp).isNone then some .security
  else none

/-- The tool definition `registerTool()` adds to document `doc` when every check passes. -/
def newTool (s : State) (t : ModelContextTool) (sig : Option Nat) (exp : List OriginArg)
    (doc : Nat) : ToolDef :=
  { id := s.nextId, name := t.name, title := t.title, description := t.description.getD "",
    inputSchema := t.inputSchema, outputSchema := t.outputSchema,
    annotations := t.annotations, behavior := t.behavior, signal := sig, doc,
    exposedOrigins := (parseOrigins exp).getD [] }

/-- Add the new tool definition to document `doc`'s tool map under a fresh tool id, and, when a
    signal was given, the abort steps that unregister it. -/
def addTool (s : State) (t : ModelContextTool) (sig : Option Nat) (exp : List OriginArg)
    (doc : Nat) : State :=
  { s with nextId := s.nextId + 1, tools := s.tools ++ [newTool s t sig exp doc],
           abortSteps := match sig with
             | some g => s.abortSteps ++ [(g, s.nextId)]
             | none   => s.abortSteps }

/-- `registerTool()` in document `doc`, awaited. The document is fully active.
    Spec: #dom-modelcontext-registertool -/
def registerTool (s : State) (t : ModelContextTool) (sig : Option Nat)
    (exp : List OriginArg := []) (doc : Nat := 0) : State × Outcome :=
  match registerToolChecks s t sig exp doc with
  | some e => (s, .err e)
  | none   => (addTool s t sig exp doc, .ok)

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
def registerAbortSync (s : State) (t : ModelContextTool) (sig : Nat)
    (exp : List OriginArg := []) (doc : Nat := 0) : State × Outcome :=
  let (s', o) := registerTool s t (some sig) exp doc
  let (s'', _) := unregisterBySignal s' sig
  (s'', if o == .ok then .err .abort else o)

/-- The `Tool` view of a tool definition, as `getTools()` in document `caller` builds it. -/
def ToolDef.view (caller : Nat) (d : ToolDef) : ToolView :=
  { name := d.name, title := d.title.getD "", description := d.description,
    inputSchema := d.inputSchema.exposed, outputSchema := d.outputSchema.exposed,
    annotations := Annotations.exposed d.annotations,
    source := if d.doc == caller then none else some d.doc }

/-- The `Tool` object `getTools()` creates for a tool definition: its tool id and name, and its
    owner document as `source` and that document's origin as `origin`. -/
def ToolDef.object (s : State) (d : ToolDef) : ToolObject :=
  ⟨d.id, d.name, d.doc, docOrigin s d.doc⟩

/-- Sort by name. Names are ASCII (`validName`), so `String` order is the spec's
    "code unit less than". -/
def sortTools (l : List ToolDef) : List ToolDef :=
  l.mergeSort (fun a b => decide (a.name ≤ b.name))

/-- Whether `getTools()` in document `caller`, given the parsed `fromOrigins`, queries document
    `target`'s tool map ("toolOwnerIsRequested"), after skipping documents not allowed to use
    "tools".
    Spec: #dom-modelcontext-gettools -/
def requested (s : State) (caller : Nat) (fromOrigins : List Origin) (target : Nat) : Bool :=
  -- "If targetDocument is not allowed to use the "tools" feature, then continue."
  docAllowed s target &&
  -- "true if targetOrigin is same origin with callerOrigin, or if from origins contains
  -- targetOrigin"
  (docOrigin s target == docOrigin s caller || fromOrigins.contains (docOrigin s target))

/-- `getTools()`'s in-parallel loop: for each document in tree order that is requested, each of
    its tool definitions that is exposed to the caller's origin, in tool map order.
    Spec: #dom-modelcontext-gettools -/
def discover (s : State) (caller : Nat) (fromOrigins : List Origin) : List ToolDef :=
  (List.range s.docs.length).flatMap fun target =>
    if requested s caller fromOrigins target then
      s.tools.filter fun d => d.doc == target &&
        -- "If tool is exposed to an origin given targetOrigin, tool definition's exposed
        -- origins, and callerOrigin returns false, then continue."
        toolIsExposed (docOrigin s target) d.exposedOrigins (docOrigin s caller)
    else []

/-- `getTools({fromOrigins})` in document `doc`: the tools `discover` finds, sorted by name.
    The sort is stable, so same-named tools from different documents stay in tree order.
    Spec: #dom-modelcontext-gettools -/
def getTools (s : State) (fromOrigins : List OriginArg := []) (doc : Nat := 0) :
    State × Outcome :=
  -- "If toolRequestor is not allowed to use the "tools" feature, then return a promise rejected
  -- with a "NotAllowedError" DOMException."
  -- (A rejected call returns no `Tool` objects; it still counts in `State.toolObjects`, which
  -- is numbered by call.)
  let rejected := { s with toolObjects := s.toolObjects ++ [[]] }
  if !docAllowed s doc then (rejected, .err .notAllowed)
  else match parseOrigins fromOrigins with
  | none => (rejected, .err .security)
  | some fo =>
    let found := sortTools (discover s doc fo)
    ({ s with toolObjects := s.toolObjects ++ [found.map (ToolDef.object s)] },
     .tools (found.map (ToolDef.view doc)))

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

/-- Look a tool id up in document `doc`'s tool map. -/
def lookup (s : State) (doc toolId : Nat) : Option ToolDef :=
  s.tools.find? fun d => d.doc == doc && d.id == toolId

/-- "tool execute steps" in document `targetDoc`: look the tool up by its tool id, then run its
    execute steps.
    Spec: #tool-execute-steps -/
def toolExecuteSteps (s : State) (targetDoc toolId : Nat) (input : Input) (json : String) :
    Except ToolExecutionError String :=
  -- "If toolMap[toolId] does not exist, then run completionSteps given null and tool not found"
  match lookup s targetDoc toolId with
  | none   => .error .toolNotFound
  | some d => invokeExecuteCallback d input json

/-- `executeTool()`'s `completionSteps`: resolve with the result, or reject with a
    `DOMException` whose name is the error's "corresponding exception name".
    Spec: #dom-modelcontext-executetool -/
def completionOutcome : Except ToolExecutionError String → Outcome
  | .ok r    => .result r
  | .error e => .err e.exceptionName

/-- `executeTool()` in document `doc`. The target document is the `Tool`'s `source`; every
    document is in the caller's traversable navigable and fully active, and no origin is opaque,
    so the checks for those never fail.
    Spec: #dom-modelcontext-executetool -/
def executeTool (s : State) (call index : Nat) (input : Input) (doc : Nat := 0) :
    State × Outcome :=
  match (s.toolObjects[call]?).bind (·[index]?) with
  | none => (s, .invalidRequest)
  | some tool =>
    -- "If callerDocument is not allowed to use the "tools" feature, then return a promise
    -- rejected with a "NotAllowedError" DOMException."
    if !docAllowed s doc then (s, .err .notAllowed)
    -- "serializing a JavaScript value to a JSON string" given inputObject
    else match input.serialize with
    | none => (s, .err .typeError)
    | some json =>
      -- In parallel: "If targetToolMap[toolId] does not exist, then ... reject promise with a
      -- "NotFoundError" DOMException"
      match lookup s tool.source tool.id with
      | none => (s, .err .notFound)
      | some d =>
        -- "If tool is exposed to an origin given targetOrigin, tool definition's exposed
        -- origins, and callerOrigin returns false, then ... reject promise with a
        -- "NotFoundError" DOMException"
        if !toolIsExposed (docOrigin s tool.source) d.exposedOrigins (docOrigin s doc) then
          (s, .err .notFound)
        -- Queue a task to run the tool execute steps.
        else (s, completionOutcome (toolExecuteSteps s tool.source tool.id input json))

/-- One call. -/
def step (s : State) : Op → State × Outcome
  | .register t sig exp doc          => registerTool s t sig exp doc
  | .registerAbortSync t sig exp doc => registerAbortSync s t sig exp doc
  | .abort sig                       => unregisterBySignal s sig
  | .getTools fo doc                 => getTools s fo doc
  | .execute c i input doc           => executeTool s c i input doc

/-- A sequence of calls, each awaited before the next. -/
def run (s : State) : List Op → State × List Outcome
  | [] => (s, [])
  | op :: ops =>
    let (s', o) := step s op
    let (s'', os) := run s' ops
    (s'', o :: os)

end WebMCP
