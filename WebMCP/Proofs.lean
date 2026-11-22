import WebMCP.Model

/-!
# Properties of the model

Each theorem holds for every state reachable from the empty model context and every sequence of
calls. Three of them discharge an `Assert` step of the spec, showing it can never fail, which is
what the spec's notes argue in prose: `execute_assert_name` (in `executeTool()`),
`unregister_assert_exists` (in "unregister a tool") and `registerTool_assert_signal` (in
`registerTool()`).
-/
namespace WebMCP

/-- What stays true of the model context and the caller's `Tool` objects at all times. -/
structure Invariant (s : State) : Prop where
  /-- Tool names in the tool map are unique. -/
  names_unique : (s.tools.map (·.name)).Nodup
  /-- A tool id identifies one tool definition. -/
  id_determines : ∀ d ∈ s.tools, ∀ d' ∈ s.tools, d.id = d'.id → d = d'
  /-- Every tool id in the tool map was issued already. -/
  ids_issued : ∀ d ∈ s.tools, d.id < s.nextId
  /-- Every tool id a `Tool` object holds was issued already. -/
  toolObjects_issued : ∀ ts ∈ s.toolObjects, ∀ o ∈ ts, o.id < s.nextId
  /-- A `Tool` object's name is the name of the registration its tool id identifies. -/
  toolObjects_named :
    ∀ ts ∈ s.toolObjects, ∀ o ∈ ts, ∀ d ∈ s.tools, d.id = o.id → d.name = o.name
  /-- Every registered tool has a valid name. -/
  names_valid : ∀ d ∈ s.tools, validName d.name = true
  /-- Every registered tool has a non-empty description. -/
  descriptions : ∀ d ∈ s.tools, d.description ≠ ""
  /-- No registered tool's registration signal has fired. -/
  signals_live : ∀ d ∈ s.tools, ∀ sig, d.signal = some sig → sig ∉ s.aborted
  /-- Every abort step whose signal has not fired yet targets a registered tool, and that tool was
      registered with that signal. -/
  abortSteps_target : ∀ p ∈ s.abortSteps, p.1 ∉ s.aborted →
    ∃ d ∈ s.tools, d.id = p.2 ∧ d.signal = some p.1

theorem invariant_init : Invariant {} := by
  constructor <;> simp

/-! ### Single steps -/

/-- `registerToolChecks` passes exactly when every one of its checks does. Adding a check to
    `registerToolChecks` means adding its condition here; the proof itself needn't change. -/
theorem registerToolChecks_eq_none {s : State} {t : ModelContextTool} {sig : Option Nat} :
    registerToolChecks s t sig = none ↔
      converts t = true ∧ hasName s t.name = false ∧ validName t.name = true ∧
      t.description ≠ some "" ∧ t.inputSchema ≠ .unserializable ∧
      t.outputSchema ≠ .unserializable ∧ ∀ g, sig = some g → g ∉ s.aborted := by
  cases sig <;> unfold registerToolChecks <;> grind

theorem registerTool_ok_iff {s : State} {t : ModelContextTool} {sig : Option Nat} :
    (registerTool s t sig).2 = .ok ↔ registerToolChecks s t sig = none := by
  unfold registerTool
  cases registerToolChecks s t sig <;> simp

theorem registerTool_of_checks {s : State} {t : ModelContextTool} {sig : Option Nat}
    (hc : registerToolChecks s t sig = none) : registerTool s t sig = (addTool s t sig, .ok) := by
  simp [registerTool, hc]

theorem registerTool_of_checks_some {s : State} {t : ModelContextTool} {sig : Option Nat} {e : Err}
    (hc : registerToolChecks s t sig = some e) : registerTool s t sig = (s, .err e) := by
  simp [registerTool, hc]

/-- A tool that passes the checks has a description, and it is not empty. -/
theorem newTool_description {s : State} {t : ModelContextTool} {sig : Option Nat}
    (hc : registerToolChecks s t sig = none) :
    some (newTool s t sig).description = t.description ∧
      (newTool s t sig).description ≠ "" := by
  obtain ⟨hconv, -, -, hdesc, -⟩ := registerToolChecks_eq_none.mp hc
  simp only [converts, Bool.and_eq_true] at hconv
  obtain ⟨dsc, hdsc⟩ := Option.isSome_iff_exists.mp hconv.1.1
  simp only [newTool, hdsc] at hdesc ⊢
  exact ⟨rfl, fun h => hdesc (h ▸ rfl)⟩

theorem mem_addTool {s : State} {t : ModelContextTool} {sig : Option Nat} {d : ToolDef} :
    d ∈ (addTool s t sig).tools ↔ d ∈ s.tools ∨ d = newTool s t sig := by
  simp [addTool]

theorem mem_addTool_abortSteps {s : State} {t : ModelContextTool} {sig : Option Nat}
    {p : Nat × Nat} :
    p ∈ (addTool s t sig).abortSteps ↔
      p ∈ s.abortSteps ∨ (some p.1 = sig ∧ p.2 = s.nextId) := by
  cases sig <;> cases p <;> simp [addTool, eq_comm]

theorem unregisterBySignal_of_fresh {s : State} {sig : Nat} (hn : sig ∉ s.aborted) :
    unregisterBySignal s sig =
      ({ s with aborted := sig :: s.aborted, tools := s.tools.filter (·.signal != some sig) },
       .ok) := by
  simp [unregisterBySignal, hn]

theorem unregisterBySignal_of_aborted {s : State} {sig : Nat} (ha : sig ∈ s.aborted) :
    unregisterBySignal s sig = (s, .ok) := by
  simp [unregisterBySignal, ha]

theorem mem_filter_signal {l : List ToolDef} {sig : Nat} {d : ToolDef} :
    d ∈ l.filter (·.signal != some sig) ↔ d ∈ l ∧ d.signal ≠ some sig := by
  simp

theorem mem_sortTools {l : List ToolDef} {d : ToolDef} : d ∈ sortTools l ↔ d ∈ l :=
  (List.mergeSort_perm _ _).mem_iff

/-! ### The invariant -/

theorem addTool_invariant {s : State} (h : Invariant s) {t : ModelContextTool} {sig : Option Nat}
    (hc : registerToolChecks s t sig = none) : Invariant (addTool s t sig) := by
  obtain ⟨-, hdup, hname, -, -, -, hsig⟩ := registerToolChecks_eq_none.mp hc
  have hdesc := (newTool_description hc).2
  have hfresh : ∀ d ∈ s.tools, d.name ≠ t.name := by
    intro d hd heq
    have := List.any_eq_false.mp hdup d hd
    simp [heq] at this
  -- The new tool's id is fresh: no tool or `Tool` object holds it yet.
  have hnew_id : ∀ d ∈ s.tools, d.id ≠ s.nextId :=
    fun d hd => Nat.ne_of_lt (h.ids_issued d hd)
  constructor
  · simp only [addTool, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨h.names_unique, by simp, ?_⟩
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_singleton] at hb
    exact hb ▸ hfresh d hd
  · intro d hd d' hd' heq
    rcases mem_addTool.mp hd with hd | rfl <;> rcases mem_addTool.mp hd' with hd' | rfl
    · exact h.id_determines d hd d' hd' heq
    · exact absurd heq (hnew_id d hd)
    · exact absurd heq.symm (hnew_id d' hd')
    · rfl
  · intro d hd
    rcases mem_addTool.mp hd with hd | rfl
    · exact Nat.lt_succ_of_lt (h.ids_issued d hd)
    · exact Nat.lt_succ_self _
  · intro ts hts o ho
    exact Nat.lt_succ_of_lt (h.toolObjects_issued ts hts o ho)
  · intro ts hts o ho d hd heq
    rcases mem_addTool.mp hd with hd | rfl
    · exact h.toolObjects_named ts hts o ho d hd heq
    · exact absurd heq.symm (Nat.ne_of_lt (h.toolObjects_issued ts hts o ho))
  · intro d hd
    rcases mem_addTool.mp hd with hd | rfl
    · exact h.names_valid d hd
    · exact hname
  · intro d hd
    rcases mem_addTool.mp hd with hd | rfl
    · exact h.descriptions d hd
    · exact hdesc
  · intro d hd g hg
    rcases mem_addTool.mp hd with hd | rfl
    · exact h.signals_live d hd g hg
    · exact hsig g hg
  · intro p hp hpa
    rcases mem_addTool_abortSteps.mp hp with hp | ⟨hg, hid⟩
    · obtain ⟨d, hd, hdp⟩ := h.abortSteps_target p hp hpa
      exact ⟨d, mem_addTool.mpr (.inl hd), hdp⟩
    · exact ⟨newTool s t sig, mem_addTool.mpr (.inr rfl), hid.symm, hg.symm⟩

theorem registerTool_invariant {s : State} (h : Invariant s) (t : ModelContextTool)
    (sig : Option Nat) : Invariant (registerTool s t sig).1 := by
  cases hc : registerToolChecks s t sig with
  | some e => rw [registerTool_of_checks_some hc]; exact h
  | none => rw [registerTool_of_checks hc]; exact addTool_invariant h hc

theorem unregisterBySignal_invariant {s : State} (h : Invariant s) (sig : Nat) :
    Invariant (unregisterBySignal s sig).1 := by
  by_cases hn : sig ∈ s.aborted
  · rw [unregisterBySignal_of_aborted hn]; exact h
  rw [unregisterBySignal_of_fresh hn]
  have mem : ∀ {d}, d ∈ s.tools.filter (·.signal != some sig) → d ∈ s.tools :=
    fun hd => (mem_filter_signal.mp hd).1
  constructor
  · exact h.names_unique.sublist ((List.filter_sublist).map _)
  · intro d hd d' hd' heq; exact h.id_determines d (mem hd) d' (mem hd') heq
  · intro d hd; exact h.ids_issued d (mem hd)
  · exact h.toolObjects_issued
  · intro ts hts o ho d hd heq; exact h.toolObjects_named ts hts o ho d (mem hd) heq
  · intro d hd; exact h.names_valid d (mem hd)
  · intro d hd; exact h.descriptions d (mem hd)
  · intro d hd g hg hga
    rcases List.mem_cons.mp hga with rfl | hga
    · exact (mem_filter_signal.mp hd).2 hg
    · exact h.signals_live d (mem hd) g hg hga
  · intro p hp hpa
    rw [List.mem_cons, not_or] at hpa
    obtain ⟨d, hd, hid, hsig⟩ := h.abortSteps_target p hp hpa.2
    refine ⟨d, mem_filter_signal.mpr ⟨hd, ?_⟩, hid, hsig⟩
    rw [hsig]
    exact fun heq => hpa.1 (Option.some.inj heq)

theorem getTools_invariant {s : State} (h : Invariant s) : Invariant (getTools s).1 := by
  constructor
  · exact h.names_unique
  · exact h.id_determines
  · exact h.ids_issued
  · simp only [getTools, List.mem_append, List.mem_singleton]
    intro ts hts o ho
    rcases hts with hts | rfl
    · exact h.toolObjects_issued ts hts o ho
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
      exact h.ids_issued d (mem_sortTools.mp hd)
  · simp only [getTools, List.mem_append, List.mem_singleton]
    intro ts hts o ho d hd heq
    rcases hts with hts | rfl
    · exact h.toolObjects_named ts hts o ho d hd heq
    · obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp ho
      exact congrArg (·.name) (h.id_determines d hd d0 (mem_sortTools.mp hd0) heq)
  · exact h.names_valid
  · exact h.descriptions
  · exact h.signals_live
  · exact h.abortSteps_target

theorem executeTool_state (s : State) (c i : Nat) (x : Input) : (executeTool s c i x).1 = s := by
  unfold executeTool
  repeat' split
  all_goals rfl

theorem registerAbortSync_invariant {s : State} (h : Invariant s) (t : ModelContextTool)
    (sig : Nat) : Invariant (registerAbortSync s t sig).1 :=
  unregisterBySignal_invariant (registerTool_invariant h t (some sig)) sig

theorem step_invariant {s : State} (h : Invariant s) (op : Op) : Invariant (step s op).1 := by
  cases op with
  | register t sig => exact registerTool_invariant h t sig
  | registerAbortSync t sig => exact registerAbortSync_invariant h t sig
  | abort sig => exact unregisterBySignal_invariant h sig
  | getTools => exact getTools_invariant h
  | execute c i x => simp only [step, executeTool_state]; exact h

/-- The invariant holds after any sequence of calls. -/
theorem run_invariant {s : State} (h : Invariant s) (ops : List Op) :
    Invariant (run s ops).1 := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih (step_invariant h op)

/-- The invariant holds in every reachable state. -/
theorem reachable_invariant (ops : List Op) : Invariant (run {} ops).1 :=
  run_invariant invariant_init ops

/-! ### `registerTool()` -/

/-- `registerTool` returns the state unchanged when it rejects: `registerTool()` makes every
    check before it adds anything. (This doesn't hold for `registerAbortSync`, whose `AbortError`
    comes after the tool was added and removed.) -/
theorem registerTool_err_state (s : State) (t : ModelContextTool) (sig : Option Nat) (e : Err)
    (h : (registerTool s t sig).2 = .err e) : (registerTool s t sig).1 = s := by
  cases hc : registerToolChecks s t sig with
  | some e' => rw [registerTool_of_checks_some hc]
  | none => rw [registerTool_of_checks hc] at h; cases h

/-- After `registerTool()` fulfills, the next `getTools()` lists a tool with the registered name,
    and its `title`, `description`, `inputSchema`, `outputSchema` and `annotations` are the ones
    passed in (an omitted title as `""`, schemas as their JSON). -/
theorem registerTool_then_getTools {s : State} {t : ModelContextTool} {sig : Option Nat}
    (h : (registerTool s t sig).2 = .ok) :
    ∃ ts, (getTools (registerTool s t sig).1).2 = .tools ts ∧
      ∃ v ∈ ts, v.name = t.name ∧ v.title = t.title.getD "" ∧
        some v.description = t.description ∧ v.inputSchema = t.inputSchema.exposed ∧
        v.outputSchema = t.outputSchema.exposed ∧
        v.annotations = Annotations.exposed t.annotations := by
  have hc := registerTool_ok_iff.mp h
  rw [registerTool_of_checks hc]
  refine ⟨_, rfl, (newTool s t sig).view, ?_, rfl, rfl, (newTool_description hc).1, rfl, rfl,
    rfl⟩
  exact List.mem_map_of_mem (mem_sortTools.mpr (mem_addTool.mpr (.inr rfl)))

/-- The spec's `Assert: signal is not aborted` in `registerTool()`: when a registration with a
    signal succeeds, that signal had not fired. It follows directly from the check just before
    it. -/
theorem registerTool_assert_signal {s : State} {t : ModelContextTool} {g : Nat}
    (h : (registerTool s t (some g)).2 = .ok) : g ∉ s.aborted :=
  (registerToolChecks_eq_none.mp (registerTool_ok_iff.mp h)).2.2.2.2.2.2 g rfl

/-! ### Unregistering through the signal -/

/-- The spec's `Assert: tool map[tool id] exists` in "unregister a tool": when a registration
    signal fires for the first time, every abort step `registerTool()` added to it finds its tool
    still in the tool map. -/
theorem unregister_assert_exists {s : State} (h : Invariant s) {sig : Nat}
    (hfresh : sig ∉ s.aborted) {id : Nat} (hstep : (sig, id) ∈ s.abortSteps) :
    ∃ d ∈ s.tools, d.id = id :=
  let ⟨d, hd, hid, _⟩ := h.abortSteps_target _ hstep hfresh
  ⟨d, hd, hid⟩

/-- Aborting a registration signal removes exactly the tools registered with that signal and
    keeps every other tool, in the same order. This holds whether or not the signal had fired
    before. -/
theorem unregisterBySignal_tools {s : State} (h : Invariant s) (sig : Nat) :
    (unregisterBySignal s sig).1.tools = s.tools.filter (·.signal != some sig) := by
  by_cases hn : sig ∈ s.aborted
  · rw [unregisterBySignal_of_aborted hn, eq_comm, List.filter_eq_self]
    intro d hd
    have := h.signals_live d hd sig
    cases hs : d.signal <;> simp_all
  · rw [unregisterBySignal_of_fresh hn]

/-! ### `getTools()` -/

/-- `getTools()` lists tools in strictly increasing order of name. -/
theorem getTools_sorted {s : State} (h : Invariant s) :
    ∃ ts, (getTools s).2 = .tools ts ∧ ts.Pairwise (fun a b => a.name < b.name) := by
  refine ⟨_, rfl, ?_⟩
  have hle := List.pairwise_mergeSort (le := fun a b : ToolDef => decide (a.name ≤ b.name))
    (fun _ _ _ hab hbc => by simp only [decide_eq_true_eq] at *; exact Std.le_trans hab hbc)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Std.le_total)
    s.tools
  have hne : (sortTools s.tools).Pairwise (fun a b => a.name ≠ b.name) :=
    List.pairwise_map.mp (((List.mergeSort_perm s.tools _).map ToolDef.name).nodup_iff.mpr
      h.names_unique)
  rw [List.pairwise_map]
  exact (hle.and hne).imp fun ⟨hab, hne⟩ => Std.lt_of_le_of_ne (of_decide_eq_true hab) hne

/-- `getTools()` never returns two tools with the same name. -/
theorem getTools_names_unique {s : State} (h : Invariant s) :
    ∃ ts, (getTools s).2 = .tools ts ∧ (ts.map (·.name)).Nodup := by
  obtain ⟨ts, hts, hsorted⟩ := getTools_sorted h
  exact ⟨ts, hts, List.pairwise_map.mpr (hsorted.imp fun hlt heq => by grind)⟩

/-! ### `executeTool()` -/

/-- A `Tool` object names the registration its tool id points to. -/
theorem toolObject_name {s : State} (h : Invariant s) {c k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[c]?).bind (·[k]?) = some tool) {d : ToolDef} (hd : d ∈ s.tools)
    (hid : d.id = tool.id) : d.name = tool.name := by
  obtain ⟨ts, hts, hk⟩ : ∃ ts, s.toolObjects[c]? = some ts ∧ ts[k]? = some tool := by
    cases hc : s.toolObjects[c]? with
    | none => simp [hc] at ht
    | some ts => exact ⟨ts, rfl, by simpa [hc] using ht⟩
  exact h.toolObjects_named ts (List.mem_of_getElem? hts) tool (List.mem_of_getElem? hk) d hd hid

/-- The spec's `Assert: tool definition's name is tool's name` in `executeTool()`. Once
    `executeTool()` on a `Tool` gets past serializing its input, it either rejects with
    `NotFoundError` or runs the execute steps of a registered tool definition with that `Tool`'s
    tool id and name, so the call runs exactly the registration `getTools()` returned. -/
theorem execute_assert_name {s : State} (h : Invariant s) {c k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[c]?).bind (·[k]?) = some tool) {x : Input} {json : String}
    (hx : x.serialize = some json) :
    (executeTool s c k x).2 = .err .notFound ∨
    ∃ d ∈ s.tools, d.id = tool.id ∧ d.name = tool.name ∧
      (executeTool s c k x).2 = completionOutcome (invokeExecuteCallback d x json) := by
  simp only [executeTool, ht, hx, toolExecuteSteps]
  cases hf : s.tools.find? (·.id == tool.id) with
  | none => exact .inl rfl
  | some d =>
    have hd := List.mem_of_find?_eq_some hf
    have hid : d.id = tool.id := by simpa using List.find?_some hf
    exact .inr ⟨d, hd, hid, toolObject_name h ht hd hid, rfl⟩

/-! ### Tool ids are never reused

  This is the property the `Tool` interface (spec PR #348) was introduced for: a `Tool` names
  one registration, so once that registration is gone, the `Tool` can never run anything again,
  even if a new tool takes the same name. -/

theorem registerTool_nextId_ge (s : State) (t : ModelContextTool) (sig : Option Nat) :
    s.nextId ≤ (registerTool s t sig).1.nextId := by
  cases hc : registerToolChecks s t sig with
  | some e => rw [registerTool_of_checks_some hc]; exact Nat.le_refl _
  | none => rw [registerTool_of_checks hc]; exact Nat.le_succ _

theorem registerTool_retired {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (t : ModelContextTool) (sig : Option Nat) : n ∉ ids (registerTool s t sig).1 := by
  cases hc : registerToolChecks s t sig with
  | some e => rw [registerTool_of_checks_some hc]; exact hn
  | none =>
    rw [registerTool_of_checks hc]
    simp only [ids, addTool, newTool, List.map_append, List.mem_append, List.map_cons,
      List.map_nil, List.mem_singleton, not_or]
    exact ⟨hn, Nat.ne_of_lt hlt⟩

theorem unregisterBySignal_retired {s : State} (n : Nat) (hn : n ∉ ids s) (sig : Nat) :
    n ∉ ids (unregisterBySignal s sig).1 := by
  by_cases ha : sig ∈ s.aborted
  · rw [unregisterBySignal_of_aborted ha]; exact hn
  · rw [unregisterBySignal_of_fresh ha]
    simp only [ids, List.mem_map, mem_filter_signal, not_exists, not_and] at hn ⊢
    exact fun d hd => hn d hd.1

theorem unregisterBySignal_nextId (s : State) (sig : Nat) :
    (unregisterBySignal s sig).1.nextId = s.nextId := by
  unfold unregisterBySignal; split <;> rfl

theorem retired_stays_retired {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (op : Op) : n < (step s op).1.nextId ∧ n ∉ ids (step s op).1 := by
  cases op with
  | register t sig =>
    exact ⟨Nat.lt_of_lt_of_le hlt (registerTool_nextId_ge s t sig),
      registerTool_retired n hlt hn t sig⟩
  | registerAbortSync t sig =>
    simp only [step, registerAbortSync]
    refine ⟨?_, unregisterBySignal_retired n (registerTool_retired n hlt hn t (some sig)) sig⟩
    rw [unregisterBySignal_nextId]
    exact Nat.lt_of_lt_of_le hlt (registerTool_nextId_ge s t (some sig))
  | abort sig =>
    simp only [step]
    exact ⟨by rw [unregisterBySignal_nextId]; exact hlt, unregisterBySignal_retired n hn sig⟩
  | getTools => exact ⟨hlt, hn⟩
  | execute c i x => simp only [step, executeTool_state]; exact ⟨hlt, hn⟩

theorem retired_stays_retired_run {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) : n ∉ ids (run s ops).1 := by
  induction ops generalizing s with
  | nil => exact hn
  | cons op ops ih =>
    have := retired_stays_retired n hlt hn op
    exact ih this.1 this.2

/-- Executing a `Tool` whose registration is gone fails with `NotFoundError` (or `TypeError`,
    if the input itself cannot be serialized), whatever the page has done since. -/
theorem stale_tool_not_found {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) (c k : Nat) (x : Input) (name : String)
    (ht : ((run s ops).1.toolObjects[c]?).bind (·[k]?) = some ⟨n, name⟩) :
    (executeTool (run s ops).1 c k x).2 = .err .notFound ∨
    (executeTool (run s ops).1 c k x).2 = .err .typeError := by
  have hgone := retired_stays_retired_run n hlt hn ops
  generalize (run s ops).1 = s' at ht hgone ⊢
  cases hx : x.serialize with
  | none => simp [executeTool, ht, hx]
  | some json =>
    have : s'.tools.find? (·.id == n) = none := by
      rw [List.find?_eq_none]
      intro d hd heq
      exact hgone (List.mem_map.mpr ⟨d, hd, by simpa using heq⟩)
    simp [executeTool, ht, hx, toolExecuteSteps, this, completionOutcome,
      ToolExecutionError.exceptionName]

end WebMCP

-- Fail the build if any theorem above comes to rest on `sorry` or an extra axiom.
/-- info: 'WebMCP.reachable_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.reachable_invariant
/-- info: 'WebMCP.getTools_names_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.getTools_names_unique
/-- info: 'WebMCP.getTools_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.getTools_sorted
/-- info: 'WebMCP.registerTool_then_getTools' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.registerTool_then_getTools
/-- info: 'WebMCP.registerTool_assert_signal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.registerTool_assert_signal
/-- info: 'WebMCP.unregister_assert_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.unregister_assert_exists
/-- info: 'WebMCP.unregisterBySignal_tools' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.unregisterBySignal_tools
/-- info: 'WebMCP.execute_assert_name' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.execute_assert_name
/-- info: 'WebMCP.stale_tool_not_found' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.stale_tool_not_found
/-- info: 'WebMCP.registerTool_err_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.registerTool_err_state
