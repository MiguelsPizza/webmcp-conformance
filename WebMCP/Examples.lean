import WebMCP.Model

/-!
# Worked examples

Hand-written traces with the outcomes the spec requires, checked when the library builds.
A change to an algorithm in the model has to update the readable examples it affects.
Each example starts with a short name in backticks, which the README's spec mapping refers to.
-/
namespace WebMCP.Examples

/-- A tool with every optional member omitted. -/
def tool (name : String) (b : Behavior := .echo) : ModelContextTool :=
  { name, title := none, description := some "d", inputSchema := .absent,
    outputSchema := .absent, annotations := none, behavior := b }

/-- Outcomes of running `ops` from an empty model context, as the harness prints them. -/
def outcomes (ops : List Op) : List String :=
  (run {} ops).2.map Outcome.render

-- `listed-and-runs`: a registered tool is listed and runs; an omitted title is exposed as ""
-- and absent schemas and annotations as null.
#guard outcomes [.register (tool "a") none, .getTools, .execute 0 0 (.obj 3)] ==
  ["ok", "tools:a||d|null|null|null", "result:{\"n\":3}"]

-- `unregistration-execution-race`, the spec's own example: an old `Tool` must not run the tool
-- re-registered under its name.
#guard outcomes [.register (tool "a") (some 0), .getTools, .abort 0, .register (tool "a") none,
    .execute 0 0 (.obj 10)] ==
  ["ok", "tools:a||d|null|null|null", "ok", "ok", "err:NotFoundError"]

-- `validation-order`: a duplicate name is reported before an invalid one, and Web IDL
-- conversion failures before both.
#guard outcomes [.register (tool "a") none, .register (tool "a") none,
    .register { tool "a" with inputSchema := .nonObject } none] ==
  ["ok", "err:InvalidStateError", "err:TypeError"]

-- `schema-before-signal`: schema serialization errors come before an already-aborted signal.
#guard outcomes [.abort 1, .register { tool "a" with outputSchema := .unserializable } (some 1)] ==
  ["ok", "err:TypeError"]

-- `abort-before-await`: aborting the signal before awaiting registerTool() rejects it, and the
-- tool is gone.
#guard outcomes [.registerAbortSync (tool "a") 2, .getTools] == ["err:AbortError", "tools:"]

-- `names`: 128 characters is the limit, and only ASCII alphanumerics, "_", "-" and "." count.
#guard outcomes [.register (tool ("".pushn 'x' 128)) none,
    .register (tool ("".pushn 'y' 129)) none, .register (tool "é") none] ==
  ["ok", "err:InvalidStateError", "err:InvalidStateError"]

-- `results`: results are serialized to JSON; undefined cannot be, and a non-object input is
-- invalid.
#guard outcomes [.register (tool "t" .returnText) none, .register (tool "u" .returnUndefined) none,
    .getTools, .execute 0 0 .omitted, .execute 0 1 .omitted, .execute 0 0 .toJSONNumber] ==
  ["ok", "ok", "tools:t||d|null|null|null;u||d|null|null|null", "result:\"hi\"",
   "err:OperationError", "err:DataError"]

-- `sorted`: getTools() sorts by code unit, so upper case comes first, and exposes schemas after
-- toJSON().
#guard outcomes [.register { tool "b" with inputSchema := .viaToJSON } none,
    .register { tool "B" with title := some "T" } none, .getTools] ==
  ["ok", "ok", "tools:B|T|d|null|null|null;b||d|{\"type\":\"string\"}|null|null"]

/-! ### Frames and origins

Documents are numbered as in `harnessDocs`: 0 and 1 share origin 0, 2 has origin 2, and 3 and 4
have origin 1, where 4's `<iframe>` doesn't delegate "tools". -/

-- `two-sided-opt-in`, the spec's own example: a cross-origin frame exposes a tool to its
-- parent's origin, and the parent sees it only once it also asks for that origin.
#guard outcomes [.register (tool "chart") none [.origin 0] 3, .getTools [] 0,
    .getTools [.origin 1] 0, .execute 1 0 (.obj 1) 0] ==
  ["ok", "tools:", "tools:chart||d|null|null|null@3", "result:{\"n\":1}"]

-- `provider-opt-in`: asking for an origin is not enough; the tool must be exposed to the
-- caller's origin too. A URL with a path names its origin.
#guard outcomes [.register (tool "w") none [] 3, .register (tool "v") none [.withPath 2] 3,
    .getTools [.origin 1] 0, .getTools [.origin 1] 2] ==
  ["ok", "ok", "tools:", "tools:v||d|null|null|null@3"]

-- `same-origin-frames`: same-origin documents see each other's tools without asking. Each
-- document has its own tool map, so names repeat across documents, in tree order.
#guard outcomes [.register (tool "a") none [] 1, .register (tool "a") none [] 0,
    .register (tool "b") none [] 0, .getTools [] 0, .getTools [] 2] ==
  ["ok", "ok", "ok", "tools:a||d|null|null|null;a||d|null|null|null@1;b||d|null|null|null",
   "tools:"]

-- `not-allowed`: a cross-origin frame whose `<iframe>` doesn't delegate "tools" can't use the
-- API, and Web IDL conversion still comes first.
#guard outcomes [.register (tool "a") none [] 4, .register { tool "a" with description := none }
    none [] 4, .getTools [] 4] ==
  ["err:NotAllowedError", "err:TypeError", "err:NotAllowedError"]

-- `security`: `exposedTo` and `fromOrigins` entries must be potentially trustworthy origins.
-- The `exposedTo` check comes after the signal check.
#guard outcomes [.register (tool "a") none [.origin 0, .insecure] 0, .abort 0,
    .register (tool "a") (some 0) [.invalid] 0, .getTools [.invalid] 0, .getTools [.insecure] 4] ==
  ["err:SecurityError", "ok", "err:AbortError", "err:SecurityError", "err:NotAllowedError"]

-- `execute-exposure`: `executeTool()` checks exposure again against the caller's own origin. A
-- same-origin document can run a `Tool` another one discovered; a document of an origin the tool
-- isn't exposed to gets `NotFoundError`, as for a tool that is gone.
#guard outcomes [.register (tool "chart") none [.origin 0] 3, .getTools [.origin 1] 0,
    .execute 0 0 (.obj 2) 1, .execute 0 0 (.obj 2) 2, .execute 0 0 (.obj 2) 4] ==
  ["ok", "tools:chart||d|null|null|null@3", "result:{\"n\":2}", "err:NotFoundError",
   "err:NotAllowedError"]

end WebMCP.Examples
