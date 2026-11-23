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
* calls started together without awaiting, with every outcome the spec's ordering allows

Spec: <https://webmachinelearning.github.io/webmcp/> at upstream commit recorded in
`spec/anchors.json`. Every definition names the algorithm it models with a `Spec:` line giving
the algorithm's anchor in `index.bs`; `tools/check-spec.cjs` fails when the text of one of those
algorithms changes upstream, so the model cannot silently fall behind.

## Abstractions

The model is deliberately smaller than the spec. Each simplification below is either harmless
for this slice or listed as not covered in the README:

* Realms and events are not modelled. Calls are awaited one at a time, except
  `Op.registerAbortSync`, which aborts the signal before the registration promise settles, and
  `Op.concurrent`, which starts several calls from one script before awaiting them. For those,
  each call's work is split into its synchronous method steps, its in-parallel steps and its
  queued tasks, at the granularity where an order the spec leaves open can change an outcome:
  when `getTools()` reads the tool maps, the order in which queued "tool execute steps" run, and
  whether a callback's abort comes before a registration's resolving task (see `concurrent`).
  Where several orders are allowed, `step` returns every outcome. The execution `signal` is
  only given in `Op.concurrent`; the callback's own `signal`, the pending tool executions maps
  and `toolcancel` are not modelled, since no outcome the harness sees depends on them.
* A callback only settles as its `Behavior` says, except that an `unregisterSelf` tool aborts its
  own registration signal first.
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
| calls started from one script, then awaited | `Op.concurrent`, `Action`, `concurrent` |
| a call's synchronous steps; its in-parallel steps and tasks | `syncAction`, `syncPhase`; `Pending`, `asyncStep`, `asyncPhase`, `callChoices` |

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
    Spec: [#tool-execution-error](https://webmachinelearning.github.io/webmcp/#tool-execution-error) -/
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
    Spec: [#permissions-policy](https://webmachinelearning.github.io/webmcp/#permissions-policy) -/
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
    Spec: [#model-context-register-tool-options](https://webmachinelearning.github.io/webmcp/#model-context-register-tool-options)
    Spec: [#model-context-get-tool-options](https://webmachinelearning.github.io/webmcp/#model-context-get-tool-options) -/
def parseOrigins (l : List OriginArg) : Option (List Origin) :=
  l.mapM OriginArg.parse

/-- "tool is exposed to an origin": the tool owner's own origin, and every origin in its
    exposed origins, may see it.
    Spec: [#tool-is-exposed-to-an-origin](https://webmachinelearning.github.io/webmcp/#tool-is-exposed-to-an-origin) -/
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
    Spec: [#serialize-a-tool-schema](https://webmachinelearning.github.io/webmcp/#serialize-a-tool-schema) -/
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
  /-- Aborts the signal its own tool was registered with, so the tool unregisters itself while
      it runs, then resolves with the input object it received. -/
  | unregisterSelf
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
    Spec: [#model-context-tool](https://webmachinelearning.github.io/webmcp/#model-context-tool) -/
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
    Spec: [#tool-definition](https://webmachinelearning.github.io/webmcp/#tool-definition) -/
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
  deriving Repr, DecidableEq

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
    Spec: [#tool-interface](https://webmachinelearning.github.io/webmcp/#tool-interface) -/
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
  deriving Repr, DecidableEq

/-- The `signal` option of an `executeTool()` started in an `Op.concurrent`. -/
inductive ExecSignal where
  /-- No `signal`. -/
  | none
  /-- A signal that a later `Action.cancel` may abort. -/
  | live
  /-- A signal that was aborted before the call. -/
  | aborted
  deriving Repr, DecidableEq

/-- One call started in an `Op.concurrent`, without awaiting it. -/
inductive Action where
  /-- `registerTool(t, {signal, exposedTo})`. -/
  | register (t : ModelContextTool) (signal : Option Nat) (exposedTo : List OriginArg)
  /-- Abort a registration signal. -/
  | abort (signal : Nat)
  /-- `getTools({fromOrigins})`. -/
  | getTools (fromOrigins : List OriginArg)
  /-- `executeTool(tool, input, {signal})` with the `index`-th `Tool` of the `call`-th
      `getTools()` before this operation. -/
  | execute (call index : Nat) (input : Input) (signal : ExecSignal)
  /-- Abort the execution signal of the `target`-th action, if it is an `execute` with a `live`
      signal that has started. -/
  | cancel (target : Nat)
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
  /-- Start each action in turn from one script in document `doc`, without awaiting any, then
      await them all. -/
  | concurrent (actions : List Action) (doc : Nat := 0)
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
  /-- The outcomes of the calls of an `Op.concurrent`, one per action, in order. -/
  | all (os : List Outcome)
  deriving Repr, BEq

/-- One `Tool` as the harness prints it: its members separated by `|`, then `@<document>` when
    its `source` is not the caller's own window. -/
def ToolView.render (v : ToolView) : String :=
  "|".intercalate [v.name, v.title, v.description, v.inputSchema, v.outputSchema, v.annotations] ++
  match v.source with
  | some d => "@" ++ toString d
  | none   => ""

/-- A string as a JSON string literal. -/
def jsonString (str : String) : String :=
  "\"" ++ String.join (str.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c == '\t' then "\\t"
    else if c.toNat < 32 then "\\u00" ++ (if c.toNat < 16 then "0" else "1") ++
      String.singleton (Nat.digitChar (c.toNat % 16))
    else String.singleton c) ++ "\""

/-- A list of strings as a JSON array. -/
def jsonArray (l : List String) : String :=
  "[" ++ ",".intercalate (l.map jsonString) ++ "]"

/-- An outcome as the harness prints it. The outcomes of an `Op.concurrent` are printed as
    `all:` and a JSON array of each action's outcome. -/
def Outcome.render : Outcome → String
  | .ok             => "ok"
  | .err e          => "err:" ++ e.name
  | .tools ts       => "tools:" ++ ";".intercalate (ts.map ToolView.render)
  | .result j       => "result:" ++ j
  | .invalidRequest => "invalid-request"
  | .all os         => "all:" ++ jsonArray (os.attach.map fun ⟨o, _⟩ => o.render)

/-- The outcomes the spec allows for one call, as the harness compares them: the outcome itself
    when there is one, or `any:` and a JSON array of every allowed outcome. -/
def renderSet : List Outcome → String
  | [o] => o.render
  | os  => "any:" ++ jsonArray (os.map Outcome.render)

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
    Spec: [#dom-modelcontext-registertool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-registertool) -/
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
    Spec: [#dom-modelcontext-registertool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-registertool) -/
def registerTool (s : State) (t : ModelContextTool) (sig : Option Nat)
    (exp : List OriginArg := []) (doc : Nat := 0) : State × Outcome :=
  match registerToolChecks s t sig exp doc with
  | some e => (s, .err e)
  | none   => (addTool s t sig exp doc, .ok)

/-- Aborting a registration signal runs its abort steps: "unregister a tool" for each tool it
    registered. A signal aborts at most once.
    Spec: [#model-context-unregister-a-tool](https://webmachinelearning.github.io/webmcp/#model-context-unregister-a-tool) -/
def unregisterBySignal (s : State) (sig : Nat) : State × Outcome :=
  if s.aborted.contains sig then (s, .ok)
  else ({ s with aborted := sig :: s.aborted,
                 tools := s.tools.filter (·.signal != some sig) }, .ok)

/-- `registerTool()` followed by aborting its signal before the promise settles. If the tool
    was registered, the abort steps unregister it and reject the promise with the abort reason
    before the queued task can resolve it.
    Spec: [#dom-modelcontext-registertool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-registertool) -/
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
    Spec: [#dom-modelcontext-gettools](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-gettools) -/
def requested (s : State) (caller : Nat) (fromOrigins : List Origin) (target : Nat) : Bool :=
  -- "If targetDocument is not allowed to use the "tools" feature, then continue."
  docAllowed s target &&
  -- "true if targetOrigin is same origin with callerOrigin, or if from origins contains
  -- targetOrigin"
  (docOrigin s target == docOrigin s caller || fromOrigins.contains (docOrigin s target))

/-- `getTools()`'s in-parallel loop: for each document in tree order that is requested, each of
    its tool definitions that is exposed to the caller's origin, in tool map order.
    Spec: [#dom-modelcontext-gettools](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-gettools) -/
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
    Spec: [#dom-modelcontext-gettools](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-gettools) -/
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
    Spec: [#invoke-the-execute-callback](https://webmachinelearning.github.io/webmcp/#invoke-the-execute-callback) -/
def callbackResult (b : Behavior) (input : Input) (json : String) :
    Except ToolExecutionError String :=
  match b with
  -- "If toolPromise was fulfilled with value v": serialize v.
  | .echo            => .ok json
  | .unregisterSelf  => .ok json
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
    Spec: [#invoke-the-execute-callback](https://webmachinelearning.github.io/webmcp/#invoke-the-execute-callback) -/
def invokeExecuteCallback (d : ToolDef) (input : Input) (json : String) :
    Except ToolExecutionError String :=
  -- "If inputObject is not an Object, then run completionSteps given null and invalid input"
  if !input.parsesToObject then .error .invalidInput
  else callbackResult d.behavior input json

/-- The registration signal the author's callback aborts while it runs, if any: an
    `unregisterSelf` tool's own, once its input has parsed to an Object and the callback is
    invoked. -/
def callbackAborts (d : ToolDef) (input : Input) : Option Nat :=
  if d.behavior == .unregisterSelf && input.parsesToObject then d.signal else none

/-- What running the author's callback does to the page: an `unregisterSelf` tool aborts its
    registration signal, which unregisters it (and every other tool registered with that signal).
    The execution itself goes on: "Unregistering a tool does not cancel an execution that has
    already reached the invoke the execute callback steps, even when the ToolExecuteCallback
    itself performs the unregistration."
    Spec: [#model-context-unregister-a-tool](https://webmachinelearning.github.io/webmcp/#model-context-unregister-a-tool) -/
def callbackEffect (s : State) (d : ToolDef) (input : Input) : State :=
  match callbackAborts d input with
  | some g => (unregisterBySignal s g).1
  | none   => s

/-- Look a tool id up in document `doc`'s tool map. -/
def lookup (s : State) (doc toolId : Nat) : Option ToolDef :=
  s.tools.find? fun d => d.doc == doc && d.id == toolId

/-- "tool execute steps" in document `targetDoc`: look the tool up by its tool id, then run its
    execute steps.
    Spec: [#tool-execute-steps](https://webmachinelearning.github.io/webmcp/#tool-execute-steps) -/
def toolExecuteSteps (s : State) (targetDoc toolId : Nat) (input : Input) (json : String) :
    Except ToolExecutionError String :=
  -- "If toolMap[toolId] does not exist, then run completionSteps given null and tool not found"
  match lookup s targetDoc toolId with
  | none   => .error .toolNotFound
  | some d => invokeExecuteCallback d input json

/-- `executeTool()`'s `completionSteps`: resolve with the result, or reject with a
    `DOMException` whose name is the error's "corresponding exception name".
    Spec: [#dom-modelcontext-executetool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-executetool) -/
def completionOutcome : Except ToolExecutionError String → Outcome
  | .ok r    => .result r
  | .error e => .err e.exceptionName

/-- The page after "tool execute steps" ran: the callback's effect, if the tool was found.
    Spec: [#tool-execute-steps](https://webmachinelearning.github.io/webmcp/#tool-execute-steps) -/
def toolExecuteEffect (s : State) (targetDoc toolId : Nat) (input : Input) : State :=
  match lookup s targetDoc toolId with
  | none   => s
  | some d => callbackEffect s d input

/-- `executeTool()` in document `doc`, awaited, with no `signal`. The target document is the
    `Tool`'s `source`; every document is in the caller's traversable navigable and fully active,
    and no origin is opaque, so the checks for those never fail. Awaited on its own, nothing runs
    between its in-parallel lookup and the queued "tool execute steps", so both see the same tool
    map. `concurrent` models what can happen in between.
    Spec: [#dom-modelcontext-executetool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-executetool) -/
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
        else (toolExecuteEffect s tool.source tool.id input,
              completionOutcome (toolExecuteSteps s tool.source tool.id input json))


/-! ### Calls that run at the same time

`Op.concurrent` starts several calls from one script and only then awaits them. Each call's
method steps run synchronously, in order; the rest of its work runs "in parallel" or in tasks
queued on the webmcp task source, after the script. Where the spec leaves the relative order of
that work open, `concurrent` gives one branch per order, and the harness accepts any of their
outcomes:

* `registerTool()` adds the tool synchronously and resolves from a queued task, so a signal
  aborted before that task runs rejects it with `AbortError`. An abort in the same script always
  comes first; one made by a tool's callback (an `unregisterSelf` tool) may come either side.
* `getTools()` reads the tool maps in parallel, at any point after its call: any state from its
  call onwards, through the end of the script and every queued tool execution.
* `executeTool()` looks the tool up in parallel and then queues "tool execute steps", which look
  it up again when the task runs, after the script. Tool ids are never reused, so the call runs
  the tool exactly when it is still registered when its task runs. The tasks of different calls
  run in any order, since each is queued from its own parallel steps.
* Aborting an execution's `signal` rejects its promise at once with `AbortError`. Cancelling
  runs in parallel too, and doesn't stop the queued "tool execute steps", so the callback still
  runs and its effect still happens. -/

/-- A call of an `Op.concurrent` after the script: settled, or waiting for its parallel steps
    and tasks. -/
inductive Pending where
  /-- Settled during the script (or not a promise). -/
  | settled (o : Outcome)
  /-- A rejected `getTools()`: no `Tool` objects. -/
  | readFailed (e : Err)
  /-- A registered tool's promise, with its signal; `aborted` once that signal fired during the
      script, which rejects the promise before its resolving task can run. -/
  | registered (signal : Option Nat) (aborted : Bool)
  /-- A `getTools()` that may read any state from index `since` of the script's states on. -/
  | reading (fromOrigins : List OriginArg) (since : Nat)
  /-- An `executeTool()` waiting for its tool execute steps; `cancelled` once its signal was
      aborted, `cancellable` if it has a signal. -/
  | executing (tool : ToolObject) (input : Input) (json : String) (cancelled cancellable : Bool)
  /-- An `execute` naming a `Tool` no earlier `getTools()` returned. -/
  | invalid
  deriving Repr

/-- A `getTools()` call's pending read, starting at the `n`-th state of the script. -/
def Pending.since (p : Pending) (n : Nat) : Pending :=
  match p with
  | .reading fo _ => .reading fo n
  | p => p

/-- The synchronous part of one action, in document `doc`, given the calls started before it:
    the state after it, its pending call, and the earlier calls after it. -/
def syncAction (doc : Nat) (s : State) (ps : List Pending) : Action → State × Pending × List Pending
  | .register t sig exp =>
    match registerToolChecks s t sig exp doc with
    | some e => (s, .settled (.err e), ps)
    | none   => (addTool s t sig exp doc, .registered sig false, ps)
  | .abort g =>
    -- The abort steps reject each promise registered with `g` that hasn't settled yet.
    ((unregisterBySignal s g).1, .settled .ok, ps.map fun p => match p with
      | .registered (some g') false => if g' == g then .registered (some g') true else p
      | p => p)
  | .getTools fo =>
    if !docAllowed s doc then (s, .readFailed .notAllowed, ps)
    else match parseOrigins fo with
    | none   => (s, .readFailed .security, ps)
    | some _ => (s, .reading fo 0, ps)
  | .execute call k x sg =>
    match (s.toolObjects[call]?).bind (·[k]?) with
    | none => (s, .invalid, ps)
    | some tool =>
      if !docAllowed s doc then (s, .settled (.err .notAllowed), ps)
      else match x.serialize with
      | none => (s, .settled (.err .typeError), ps)
      | some json =>
        -- "If signal is aborted, then return a promise rejected with signal's abort reason."
        if sg == .aborted then (s, .settled (.err .abort), ps)
        else (s, .executing tool x json false (sg == .live), ps)
  | .cancel k =>
    -- The abort steps: "Reject promise with signal's abort reason."
    (s, .settled .ok, ps.mapIdx fun i p => match p with
      | .executing tool x json false true => if i == k then .executing tool x json true true else p
      | p => p)

/-- The script of an `Op.concurrent`: every action's synchronous part, in order. Returns the
    state at the end, the pending calls, and the state in which each action was made followed
    by the state at the end. -/
def syncPhase (doc : Nat) : State → List Pending → List State → List Action →
    State × List Pending × List State
  | s, ps, hist, [] => (s, ps, hist ++ [s])
  | s, ps, hist, a :: as =>
    let (s', p, ps') := syncAction doc s ps a
    -- A `getTools()` can read the state it was called in, or any later one.
    syncPhase doc s' (ps' ++ [p.since hist.length]) (hist ++ [s]) as

/-- The queued "tool execute steps" of the `i`-th call, if it is an `executeTool()` still
    waiting: its outcome, the state after it, and the registration signal its callback aborted.
    Spec: [#dom-modelcontext-executetool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-executetool)
    Spec: [#tool-execute-steps](https://webmachinelearning.github.io/webmcp/#tool-execute-steps) -/
def asyncStep (doc : Nat) (s : State) (p : Pending) : State × Option Outcome × Option Nat :=
  match p with
  | .executing tool x json cancelled _ =>
    let (s', o, g) := match lookup s tool.source tool.id with
      -- "If toolMap[toolId] does not exist, then run completionSteps given null and tool not
      -- found": whether the in-parallel lookup or the task's finds it gone.
      | none => (s, Outcome.err .notFound, none)
      | some d =>
        if !toolIsExposed (docOrigin s tool.source) d.exposedOrigins (docOrigin s doc) then
          (s, .err .notFound, none)
        else (callbackEffect s d x, completionOutcome (invokeExecuteCallback d x json),
              callbackAborts d x)
    -- A cancelled call was already rejected with the abort reason.
    (s', some (if cancelled then .err .abort else o), g)
  | _ => (s, none, none)

/-- The tasks of the waiting `executeTool()` calls, run in the order `order`. Returns the state
    at the end, each call's outcome, the state after each task, and the signals the callbacks
    aborted. -/
def asyncPhase (doc : Nat) (ps : List Pending) : State → List Nat →
    State × List (Nat × Outcome) × List State × List Nat
  | s, [] => (s, [], [], [])
  | s, i :: is =>
    let (s', o, g) := asyncStep doc s (ps[i]?.getD .invalid)
    let (s'', os, hist, gs) := asyncPhase doc ps s' is
    (s'', (o.map fun o => [(i, o)]).getD [] ++ os, s' :: hist, g.toList ++ gs)

/-- Insert `x` at every position of a list. -/
def insertEverywhere (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (y :: ·)

/-- Every order of a list. -/
def orders : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (orders xs).flatMap (insertEverywhere x)

/-- Every way to pick one element of each list. -/
def choices {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | c :: cs => c.flatMap fun x => (choices cs).map (x :: ·)

/-- What the `i`-th call of an `Op.concurrent` can settle with, given the script's states
    `hist`, the states after the tool executions `ahist`, the executions' outcomes `ex`, and the
    signals their callbacks aborted `gs`: each allowed outcome, with the `Tool` objects it
    returns for a `getTools()`. -/
def callChoices (doc : Nat) (hist ahist : List State) (ex : List (Nat × Outcome))
    (gs : List Nat) (i : Nat) : Pending → List (Outcome × Option (List ToolObject))
  | .settled o => [(o, none)]
  | .readFailed e => [(.err e, some [])]
  | .registered sig ab =>
    if ab then [(.err .abort, none)]
    -- A callback aborted the signal: before or after the task that resolves the promise.
    else if (sig.map gs.contains).getD false then [(.ok, none), (.err .abort, none)]
    else [(.ok, none)]
  | .reading fo since =>
    ((hist.drop since ++ ahist).map fun st =>
      let r := getTools st fo doc
      (r.2, some (r.1.toolObjects.getLastD [])))
  | .executing .. => [((ex.lookup i).getD .invalidRequest, none)]
  | .invalid => [(.invalidRequest, none)]

/-- `Op.concurrent`: every allowed outcome, with the state it leaves. Each `getTools()` call's
    `Tool` objects are added to `State.toolObjects` in the order of the actions, and a rejected
    one adds none, as for `getTools`.
    Spec: [#dom-modelcontext-registertool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-registertool)
    Spec: [#dom-modelcontext-gettools](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-gettools)
    Spec: [#dom-modelcontext-executetool](https://webmachinelearning.github.io/webmcp/#dom-modelcontext-executetool) -/
def concurrent (s : State) (actions : List Action) (doc : Nat) : List (State × Outcome) :=
  let (sEnd, ps, hist) := syncPhase doc s [] [] actions
  if ps.any (fun p => match p with | .invalid => true | _ => false) then [(s, .invalidRequest)]
  else
    let waiting := (List.range ps.length).filter fun i =>
      match ps[i]? with | some (.executing ..) => true | _ => false
    (orders waiting).flatMap fun order =>
      let (sA, ex, ahist, gs) := asyncPhase doc ps sEnd order
      (choices ((List.range ps.length).map fun i =>
          callChoices doc hist ahist ex gs i (ps[i]?.getD .invalid))).map fun picked =>
        ({ sA with toolObjects := sA.toolObjects ++ picked.filterMap (·.2) },
         .all (picked.map (·.1)))

/-- One operation: every outcome the spec allows, each with the state it leaves. Every operation
    but `Op.concurrent` has exactly one. -/
def step (s : State) : Op → List (State × Outcome)
  | .register t sig exp doc          => [registerTool s t sig exp doc]
  | .registerAbortSync t sig exp doc => [registerAbortSync s t sig exp doc]
  | .abort sig                       => [unregisterBySignal s sig]
  | .getTools fo doc                 => [getTools s fo doc]
  | .execute c i input doc           => [executeTool s c i input doc]
  | .concurrent as doc               => concurrent s as doc

/-- A sequence of operations, each awaited before the next: every allowed sequence of outcomes,
    with the state it leaves. -/
def run (s : State) : List Op → List (State × List Outcome)
  | [] => [(s, [])]
  | op :: ops =>
    (step s op).flatMap fun (s', o) => (run s' ops).map fun (s'', os) => (s'', o :: os)

/-- For each operation, the outcomes the spec allows for it, from any of the states `ss`. This
    is what the oracle answers: it keeps the distinct states after each operation, not the whole
    sequences of outcomes, so it doesn't say which outcomes of one operation go with which of a
    later one. -/
def explore (ss : List State) : List Op → List (List Outcome)
  | [] => []
  | op :: ops =>
    let next := ss.flatMap (step · op)
    (next.map (·.2)).eraseDups :: explore (next.map (·.1)).eraseDups ops

end WebMCP
