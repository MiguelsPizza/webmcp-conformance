# Reading the Lean

You don't need to know Lean to follow `WebMCP/Model.lean` against the spec. Each definition's docstring links the spec algorithm (`Spec: [#anchor](…)`), and each check inside it quotes the step it models. The module doc at the top of the file has a table from spec terms (tool definition, `Tool`, tool id, tool execution error) to Lean names, and [the spec mapping](spec-mapping.md) goes from each spec anchor to its definitions, theorems and examples. The syntax that comes up most:

| Lean | Roughly, in JavaScript |
|---|---|
| `def f (s : State) (t : ModelContextTool) : Outcome := ...` | `function f(s, t) { return ... }`, with types |
| `structure ToolDef where id : Nat ...` | a plain object type with those fields |
| `inductive Err where \| typeError \| abort ...` | an enum (each case can carry data) |
| `.err .abort` | `{kind: "err", error: "AbortError"}` |
| `Except ToolExecutionError String`, `.ok r`, `.error e` | a result `r` or a failure reason `e`, like a settled promise |
| `Option String`, `some x`, `none` | a value that may be absent: `x` or `null` |
| `match x with \| some v => a \| none => b` | `x != null ? a : b`, with `v = x` |
| `{ s with tools := ts }` | `{...s, tools: ts}` |
| `(·.name)` | `t => t.name` |
| `⟨d.id, d.name⟩` | build a structure from its fields in order: `{id: d.id, name: d.name}` |
| `l[i]?` | `l[i]`, giving `none` when out of range |
| `xs.filter p`, `xs.find? p`, `xs.map f` | `xs.filter(p)`, `xs.find(p)`, `xs.map(f)` |
| `a && b`, `!a`, `==`, `!=` | the same as in JavaScript |

`Proofs.lean` is harder going and you don't need to read the proofs: each theorem's docstring says in English what it shows, and Lean checks the proof when the project builds.
