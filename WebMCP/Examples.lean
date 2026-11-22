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

end WebMCP.Examples
