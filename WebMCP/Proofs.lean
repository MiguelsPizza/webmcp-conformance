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

/-- What stays true of the model contexts and the callers' `Tool` objects at all times. -/
structure Invariant (s : State) : Prop where
  /-- Tool names in each document's tool map are unique. -/
  names_unique : s.tools.Pairwise fun a b => a.doc = b.doc → a.name ≠ b.name
  /-- A tool id identifies one tool definition. -/
  id_determines : ∀ d ∈ s.tools, ∀ d' ∈ s.tools, d.id = d'.id → d = d'
  /-- Every tool id in the tool map was issued already. -/
  ids_issued : ∀ d ∈ s.tools, d.id < s.nextId
  /-- Every tool id a `Tool` object holds was issued already. -/
  toolObjects_issued : ∀ ts ∈ s.toolObjects, ∀ o ∈ ts, o.id < s.nextId
  /-- A `Tool` object's name and source are the name and document of the registration its tool id
      identifies. -/
  toolObjects_named :
    ∀ ts ∈ s.toolObjects, ∀ o ∈ ts, ∀ d ∈ s.tools, d.id = o.id → d.name = o.name ∧ d.doc = o.source
  /-- A `Tool` object's origin is its source document's origin. -/
  toolObjects_origin : ∀ ts ∈ s.toolObjects, ∀ o ∈ ts, o.origin = docOrigin s o.source
  /-- Every tool is registered in a document allowed to use "tools". -/
  tools_allowed : ∀ d ∈ s.tools, docAllowed s d.doc = true
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
theorem registerToolChecks_eq_none {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} :
    registerToolChecks s t sig exp doc = none ↔
      converts t = true ∧ docAllowed s doc = true ∧ hasName s doc t.name = false ∧
      validName t.name = true ∧
      t.description ≠ some "" ∧ t.inputSchema ≠ .unserializable ∧
      t.outputSchema ≠ .unserializable ∧ (∀ g, sig = some g → g ∉ s.aborted) ∧
      (parseOrigins exp).isNone = false := by
  cases sig <;> unfold registerToolChecks <;> grind (splits := 24)

theorem registerTool_ok_iff {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} :
    (registerTool s t sig exp doc).2 = .ok ↔ registerToolChecks s t sig exp doc = none := by
  unfold registerTool
  cases registerToolChecks s t sig exp doc <;> simp

theorem registerTool_of_checks {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} (hc : registerToolChecks s t sig exp doc = none) :
    registerTool s t sig exp doc = (addTool s t sig exp doc, .ok) := by
  simp [registerTool, hc]

theorem registerTool_of_checks_some {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} {e : Err}
    (hc : registerToolChecks s t sig exp doc = some e) :
    registerTool s t sig exp doc = (s, .err e) := by
  simp [registerTool, hc]

/-- A tool that passes the checks has a description, and it is not empty. -/
theorem newTool_description {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} (hc : registerToolChecks s t sig exp doc = none) :
    some (newTool s t sig exp doc).description = t.description ∧
      (newTool s t sig exp doc).description ≠ "" := by
  obtain ⟨hconv, -, -, -, hdesc, -⟩ := registerToolChecks_eq_none.mp hc
  simp only [converts, Bool.and_eq_true] at hconv
  obtain ⟨dsc, hdsc⟩ := Option.isSome_iff_exists.mp hconv.1.1
  simp only [newTool, hdsc] at hdesc ⊢
  exact ⟨rfl, fun h => hdesc (h ▸ rfl)⟩

theorem mem_addTool {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} {d : ToolDef} :
    d ∈ (addTool s t sig exp doc).tools ↔ d ∈ s.tools ∨ d = newTool s t sig exp doc := by
  simp [addTool]

theorem mem_addTool_abortSteps {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} {p : Nat × Nat} :
    p ∈ (addTool s t sig exp doc).abortSteps ↔
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

/-- A document that is allowed to use "tools" is in the frame tree. -/
theorem lt_of_docAllowed {s : State} {doc : Nat} (h : docAllowed s doc = true) :
    doc < s.docs.length := by
  unfold docAllowed at h
  cases hd : s.docs[doc]? with
  | none => simp [hd] at h
  | some _ => exact (List.getElem?_eq_some_iff.mp hd).1

/-- What `discover` finds: registered tools in requested documents that are exposed to the
    caller's origin. -/
theorem mem_discover {s : State} {c : Nat} {fo : List Origin} {d : ToolDef} :
    d ∈ discover s c fo ↔ d ∈ s.tools ∧ d.doc < s.docs.length ∧
      requested s c fo d.doc = true ∧
      toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s c) = true := by
  simp only [discover, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, hd⟩
    split at hd
    · simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨hd, rfl, hx⟩ := hd
      exact ⟨hd, hi, by assumption, hx⟩
    · simp at hd
  · rintro ⟨hd, hi, hr, hx⟩
    refine ⟨d.doc, hi, ?_⟩
    simp [hr, hd, hx]

/-! ### The invariant -/

theorem hasName_false {s : State} {doc : Nat} {n : String} (h : hasName s doc n = false) :
    ∀ d ∈ s.tools, d.doc = doc → d.name ≠ n := by
  intro d hd hdoc heq
  have := List.any_eq_false.mp h d hd
  simp [hdoc, heq] at this

theorem addTool_invariant {s : State} (h : Invariant s) {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} (hc : registerToolChecks s t sig exp doc = none) :
    Invariant (addTool s t sig exp doc) := by
  obtain ⟨-, hallowed, hdup, hname, -, -, -, hsig, -⟩ := registerToolChecks_eq_none.mp hc
  have hdesc := (newTool_description hc).2
  have hfresh := hasName_false hdup
  -- The new tool's id is fresh: no tool or `Tool` object holds it yet.
  have hnew_id : ∀ d ∈ s.tools, d.id ≠ s.nextId :=
    fun d hd => Nat.ne_of_lt (h.ids_issued d hd)
  constructor
  · simp only [addTool]
    refine List.pairwise_append.mpr ⟨h.names_unique, by simp, ?_⟩
    intro a ha b hb hdoc
    simp only [List.mem_singleton] at hb
    subst hb
    exact hfresh a ha hdoc
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
  · exact h.toolObjects_origin
  · intro d hd
    rcases mem_addTool.mp hd with hd | rfl
    · exact h.tools_allowed d hd
    · exact hallowed
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
    · exact ⟨newTool s t sig exp doc, mem_addTool.mpr (.inr rfl), hid.symm, hg.symm⟩

theorem registerTool_invariant {s : State} (h : Invariant s) (t : ModelContextTool)
    (sig : Option Nat) (exp : List OriginArg) (doc : Nat) :
    Invariant (registerTool s t sig exp doc).1 := by
  cases hc : registerToolChecks s t sig exp doc with
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
  · exact h.names_unique.sublist List.filter_sublist
  · intro d hd d' hd' heq; exact h.id_determines d (mem hd) d' (mem hd') heq
  · intro d hd; exact h.ids_issued d (mem hd)
  · exact h.toolObjects_issued
  · intro ts hts o ho d hd heq; exact h.toolObjects_named ts hts o ho d (mem hd) heq
  · exact h.toolObjects_origin
  · intro d hd; exact h.tools_allowed d (mem hd)
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

/-- The state after a `getTools()` that fulfills: the new `Tool` objects are appended. -/
theorem getTools_state {s : State} {fromOrigins : List OriginArg} {c : Nat} :
    (getTools s fromOrigins c).1 = { s with toolObjects := s.toolObjects ++ [[]] } ∨
    ∃ fo, parseOrigins fromOrigins = some fo ∧
      (getTools s fromOrigins c).1 =
        { s with toolObjects :=
            s.toolObjects ++ [(sortTools (discover s c fo)).map (ToolDef.object s)] } := by
  unfold getTools
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · exact .inr ⟨_, by assumption, rfl⟩

theorem getTools_invariant {s : State} (h : Invariant s) (fromOrigins : List OriginArg)
    (c : Nat) : Invariant (getTools s fromOrigins c).1 := by
  rcases getTools_state (s := s) (fromOrigins := fromOrigins) (c := c) with hs | ⟨fo, -, hs⟩
  · rw [hs]
    constructor <;> simp only [List.mem_append, List.mem_singleton]
    all_goals first
      | exact h.names_unique | exact h.id_determines | exact h.ids_issued | exact h.tools_allowed
      | exact h.names_valid | exact h.descriptions | exact h.signals_live
      | exact h.abortSteps_target
      | (intro ts hts o ho; rcases hts with hts | rfl
         · first
           | exact h.toolObjects_issued ts hts o ho
           | exact h.toolObjects_origin ts hts o ho
         · simp at ho)
      | (intro ts hts o ho d hd heq; rcases hts with hts | rfl
         · exact h.toolObjects_named ts hts o ho d hd heq
         · simp at ho)
  rw [hs]
  have hmem : ∀ o ∈ (sortTools (discover s c fo)).map (ToolDef.object s),
      ∃ d ∈ s.tools, o = d.object s := by
    intro o ho
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
    exact ⟨d, (mem_discover.mp (mem_sortTools.mp hd)).1, rfl⟩
  constructor
  · exact h.names_unique
  · exact h.id_determines
  · exact h.ids_issued
  · simp only [List.mem_append, List.mem_singleton]
    intro ts hts o ho
    rcases hts with hts | rfl
    · exact h.toolObjects_issued ts hts o ho
    · obtain ⟨d, hd, rfl⟩ := hmem o ho
      exact h.ids_issued d hd
  · simp only [List.mem_append, List.mem_singleton]
    intro ts hts o ho d hd heq
    rcases hts with hts | rfl
    · exact h.toolObjects_named ts hts o ho d hd heq
    · obtain ⟨d0, hd0, rfl⟩ := hmem o ho
      have := h.id_determines d hd d0 hd0 heq
      subst this
      exact ⟨rfl, rfl⟩
  · simp only [List.mem_append, List.mem_singleton]
    intro ts hts o ho
    rcases hts with hts | rfl
    · exact h.toolObjects_origin ts hts o ho
    · obtain ⟨d0, -, rfl⟩ := hmem o ho
      rfl
  · exact h.tools_allowed
  · exact h.names_valid
  · exact h.descriptions
  · exact h.signals_live
  · exact h.abortSteps_target

theorem executeTool_state (s : State) (c i : Nat) (x : Input) (doc : Nat) :
    (executeTool s c i x doc).1 = s := by
  unfold executeTool
  repeat' split
  all_goals rfl

theorem registerAbortSync_invariant {s : State} (h : Invariant s) (t : ModelContextTool)
    (sig : Nat) (exp : List OriginArg) (doc : Nat) :
    Invariant (registerAbortSync s t sig exp doc).1 :=
  unregisterBySignal_invariant (registerTool_invariant h t (some sig) exp doc) sig

theorem step_invariant {s : State} (h : Invariant s) (op : Op) : Invariant (step s op).1 := by
  cases op with
  | register t sig exp doc => exact registerTool_invariant h t sig exp doc
  | registerAbortSync t sig exp doc => exact registerAbortSync_invariant h t sig exp doc
  | abort sig => exact unregisterBySignal_invariant h sig
  | getTools fo doc => exact getTools_invariant h fo doc
  | execute c i x doc => simp only [step, executeTool_state]; exact h

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
theorem registerTool_err_state (s : State) (t : ModelContextTool) (sig : Option Nat)
    (exp : List OriginArg) (doc : Nat) (e : Err)
    (h : (registerTool s t sig exp doc).2 = .err e) : (registerTool s t sig exp doc).1 = s := by
  cases hc : registerToolChecks s t sig exp doc with
  | some e' => rw [registerTool_of_checks_some hc]
  | none => rw [registerTool_of_checks hc] at h; cases h

/-- The new tool is in its own document's `discover` list with no `fromOrigins`. -/
theorem newTool_discovered {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat} (hc : registerToolChecks s t sig exp doc = none) :
    newTool s t sig exp doc ∈ discover (addTool s t sig exp doc) doc [] := by
  obtain ⟨-, hallowed, -⟩ := registerToolChecks_eq_none.mp hc
  refine mem_discover.mpr ⟨mem_addTool.mpr (.inr rfl), lt_of_docAllowed hallowed, ?_, ?_⟩ <;>
    simp [requested, toolIsExposed, newTool, docAllowed, docOrigin, addTool] <;>
    simpa [docAllowed] using hallowed

/-- After `registerTool()` fulfills, the next `getTools()` in the same document lists a tool with
    the registered name, as its own (`source` is the caller), and its `title`, `description`,
    `inputSchema`, `outputSchema` and `annotations` are the ones passed in (an omitted title as
    `""`, schemas as their JSON). -/
theorem registerTool_then_getTools {s : State} {t : ModelContextTool} {sig : Option Nat}
    {exp : List OriginArg} {doc : Nat}
    (h : (registerTool s t sig exp doc).2 = .ok) :
    ∃ ts, (getTools (registerTool s t sig exp doc).1 [] doc).2 = .tools ts ∧
      ∃ v ∈ ts, v.name = t.name ∧ v.title = t.title.getD "" ∧
        some v.description = t.description ∧ v.inputSchema = t.inputSchema.exposed ∧
        v.outputSchema = t.outputSchema.exposed ∧
        v.annotations = Annotations.exposed t.annotations ∧ v.source = none := by
  have hc := registerTool_ok_iff.mp h
  obtain ⟨-, hallowed, -⟩ := registerToolChecks_eq_none.mp hc
  rw [registerTool_of_checks hc]
  have ha : docAllowed (addTool s t sig exp doc) doc = true := hallowed
  refine ⟨_, by simp [getTools, ha, parseOrigins]; rfl, (newTool s t sig exp doc).view doc, ?_,
    rfl, rfl, (newTool_description hc).1, rfl, rfl, rfl, by simp [ToolDef.view, newTool]⟩
  exact List.mem_map_of_mem (mem_sortTools.mpr (newTool_discovered hc))

/-- The spec's `Assert: signal is not aborted` in `registerTool()`: when a registration with a
    signal succeeds, that signal had not fired. It follows directly from the check just before
    it. -/
theorem registerTool_assert_signal {s : State} {t : ModelContextTool} {g : Nat}
    {exp : List OriginArg} {doc : Nat}
    (h : (registerTool s t (some g) exp doc).2 = .ok) : g ∉ s.aborted :=
  (registerToolChecks_eq_none.mp (registerTool_ok_iff.mp h)).2.2.2.2.2.2.2.1 g rfl

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

/-! ### `getTools()` and exposure -/

/-- The tools `getTools()` resolves with, and the `Tool` objects it creates: when it fulfills,
    `fromOrigins` parsed, and the result is `discover`'s list sorted by name. -/
theorem getTools_tools {s : State} {fromOrigins : List OriginArg} {c : Nat}
    {ts : List ToolView} (h : (getTools s fromOrigins c).2 = .tools ts) :
    ∃ fo, parseOrigins fromOrigins = some fo ∧ docAllowed s c = true ∧
      ts = (sortTools (discover s c fo)).map (ToolDef.view c) ∧
      (getTools s fromOrigins c).1.toolObjects =
        s.toolObjects ++ [(sortTools (discover s c fo)).map (ToolDef.object s)] := by
  unfold getTools at h ⊢
  split at h
  · cases h
  · rename_i ha
    split at h
    · cases h
    · rename_i fo hfo
      cases h
      exact ⟨fo, hfo, by simpa using ha, rfl, by simp [ha]⟩

/-- **A tool is only ever discovered by an origin it is exposed to.** Every `Tool` that
    `getTools()` in document `c` returns is a registration in a document allowed to use "tools"
    that is either same origin with `c` or listed in `fromOrigins` (the consumer's opt-in), and
    the tool is exposed to `c`'s origin: `c` is same origin with the tool owner or listed in its
    `exposedTo` (the provider's opt-in). -/
theorem getTools_exposed {s : State} {fromOrigins : List OriginArg} {c : Nat}
    {ts : List ToolView} (h : (getTools s fromOrigins c).2 = .tools ts) :
    ∃ fo, parseOrigins fromOrigins = some fo ∧
      ∃ found : List ToolDef, ts = found.map (ToolDef.view c) ∧
        (getTools s fromOrigins c).1.toolObjects =
          s.toolObjects ++ [found.map (ToolDef.object s)] ∧
        ∀ d ∈ found, d ∈ s.tools ∧ docAllowed s d.doc = true ∧
          (docOrigin s d.doc = docOrigin s c ∨ docOrigin s d.doc ∈ fo) ∧
          toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s c) = true := by
  obtain ⟨fo, hfo, -, hts, hobj⟩ := getTools_tools h
  refine ⟨fo, hfo, _, hts, hobj, fun d hd => ?_⟩
  obtain ⟨hd, -, hr, hx⟩ := mem_discover.mp (mem_sortTools.mp hd)
  simp only [requested, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem]
    at hr
  exact ⟨hd, hr.1, hr.2, hx⟩

/-- With no `fromOrigins`, `getTools()` only returns tools from documents same origin with the
    caller. -/
theorem getTools_same_origin {s : State} {c : Nat} {ts : List ToolView}
    (h : (getTools s [] c).2 = .tools ts) :
    ∃ found : List ToolDef, ts = found.map (ToolDef.view c) ∧
      ∀ d ∈ found, docOrigin s d.doc = docOrigin s c := by
  obtain ⟨fo, hfo, found, hts, -, hall⟩ := getTools_exposed h
  simp only [parseOrigins, List.mapM_nil, Option.pure_def, Option.some.injEq] at hfo
  subst hfo
  exact ⟨found, hts, fun d hd => (hall d hd).2.2.1.resolve_right (by simp)⟩

/-- `getTools()` lists tools in increasing order of name, and strictly increasing among the
    tools of one document (`source`). Tools from different documents may share a name; the sort
    is stable, so they come in tree order. -/
theorem getTools_sorted {s : State} (h : Invariant s) {fromOrigins : List OriginArg} {c : Nat}
    {ts : List ToolView} (hts : (getTools s fromOrigins c).2 = .tools ts) :
    ts.Pairwise fun a b => a.name ≤ b.name ∧ (a.source = b.source → a.name < b.name) := by
  obtain ⟨fo, -, -, rfl, -⟩ := getTools_tools hts
  have hle := List.pairwise_mergeSort (le := fun a b : ToolDef => decide (a.name ≤ b.name))
    (fun _ _ _ hab hbc => by simp only [decide_eq_true_eq] at *; exact Std.le_trans hab hbc)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Std.le_total)
    (discover s c fo)
  -- Within one document, discovered names are distinct.
  have hdisc : (discover s c fo).Pairwise fun a b => a.doc = b.doc → a.name ≠ b.name := by
    unfold discover
    refine List.pairwise_flatMap.mpr ⟨fun i _ => ?_, ?_⟩
    · split
      · exact h.names_unique.sublist List.filter_sublist
      · exact List.Pairwise.nil
    · refine (List.pairwise_lt_range (n := s.docs.length)).imp fun {i j} hij => ?_
      intro x hx y hy hdoc
      split at hx
      · split at hy
        · simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hx hy
          exact absurd (hx.2.1 ▸ hy.2.1 ▸ hdoc) (Nat.ne_of_lt hij)
        · simp at hy
      · simp at hx
  have hne : (sortTools (discover s c fo)).Pairwise
      fun a b => a.doc = b.doc → a.name ≠ b.name :=
    ((List.mergeSort_perm _ _).pairwise_iff fun {a b} hab hdoc heq =>
      hab hdoc.symm heq.symm).mpr hdisc
  rw [List.pairwise_map]
  refine (hle.and hne).imp fun ⟨hab, hne⟩ => ?_
  have hab := of_decide_eq_true hab
  refine ⟨hab, fun hsrc => Std.lt_of_le_of_ne hab (hne ?_)⟩
  simp only [ToolDef.view] at hsrc
  split at hsrc <;> split at hsrc <;> simp_all

/-- `getTools()` never returns two tools with the same name from the same document. -/
theorem getTools_names_unique {s : State} (h : Invariant s) {fromOrigins : List OriginArg}
    {c : Nat} {ts : List ToolView} (hts : (getTools s fromOrigins c).2 = .tools ts) :
    ts.Pairwise fun a b => a.source = b.source → a.name ≠ b.name :=
  (getTools_sorted h hts).imp fun ⟨_, hlt⟩ hsrc heq => by
    have := hlt hsrc; rw [heq] at this; exact Std.lt_irrefl this

/-- A document not allowed to use "tools" never has tools, so no caller ever discovers one
    there. -/
theorem getTools_not_from_disallowed {s : State} {fromOrigins : List OriginArg} {c : Nat}
    {ts : List ToolView} (hts : (getTools s fromOrigins c).2 = .tools ts) :
    ∀ v ∈ ts, ∀ d, v.source = some d → docAllowed s d = true := by
  obtain ⟨fo, -, found, rfl, -, hall⟩ := getTools_exposed hts
  intro v hv d hsrc
  obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hv
  simp only [ToolDef.view] at hsrc
  split at hsrc
  · cases hsrc
  · cases hsrc; exact (hall d0 hd0).2.1

/-! ### `executeTool()` -/

/-- A `Tool` object names the registration its tool id points to. -/
theorem toolObject_named {s : State} (h : Invariant s) {c k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[c]?).bind (·[k]?) = some tool) {d : ToolDef} (hd : d ∈ s.tools)
    (hid : d.id = tool.id) : d.name = tool.name ∧ d.doc = tool.source ∧
      tool.origin = docOrigin s tool.source := by
  obtain ⟨ts, hts, hk⟩ : ∃ ts, s.toolObjects[c]? = some ts ∧ ts[k]? = some tool := by
    cases hc : s.toolObjects[c]? with
    | none => simp [hc] at ht
    | some ts => exact ⟨ts, rfl, by simpa [hc] using ht⟩
  have hm := List.mem_of_getElem? hts
  have ho := List.mem_of_getElem? hk
  exact ⟨(h.toolObjects_named ts hm tool ho d hd hid).1,
    (h.toolObjects_named ts hm tool ho d hd hid).2, h.toolObjects_origin ts hm tool ho⟩

theorem mem_lookup {s : State} {doc id : Nat} {d : ToolDef} (h : lookup s doc id = some d) :
    d ∈ s.tools ∧ d.doc = doc ∧ d.id = id := by
  have hm := List.mem_of_find?_eq_some h
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨hm, this⟩

/-- What `executeTool()` in document `c` can do with a `Tool`: reject before running anything
    (`NotAllowedError`, `TypeError` or `NotFoundError`), or run the execute steps of the
    registration the `Tool` identifies, in the `Tool`'s source document, when that registration
    is exposed to `c`'s origin. -/
theorem executeTool_cases {s : State} {call k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) (x : Input) (c : Nat) :
    (executeTool s call k x c).2 = .err .notAllowed ∨
    (executeTool s call k x c).2 = .err .typeError ∨
    (executeTool s call k x c).2 = .err .notFound ∨
    ∃ d ∈ s.tools, ∃ json, d.id = tool.id ∧ d.doc = tool.source ∧ x.serialize = some json ∧
      toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s c) = true ∧
      (executeTool s call k x c).2 = completionOutcome (invokeExecuteCallback d x json) := by
  unfold executeTool
  simp only [ht]
  split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · rename_i json hx
      split
      · exact .inr (.inr (.inl rfl))
      · rename_i d hl
        obtain ⟨hd, hdoc, hid⟩ := mem_lookup hl
        split
        · exact .inr (.inr (.inl rfl))
        · rename_i hexp
          refine .inr (.inr (.inr ⟨d, hd, json, hid, hdoc, hx, ?_, ?_⟩))
          · rw [hdoc]; simpa using hexp
          · simp [toolExecuteSteps, hl]

/-- **A tool is never run for an origin it is not exposed to.** If the registration a `Tool`
    identifies is not exposed to the origin of the document calling `executeTool()`, the call
    rejects with `NotAllowedError`, `TypeError` or `NotFoundError` and the tool's `execute`
    callback does not run, whatever document handed the caller the `Tool`. -/
theorem executeTool_not_exposed {s : State} {call k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) (x : Input) (c : Nat)
    (hnot : ∀ d ∈ s.tools, d.id = tool.id →
      toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s c) = false) :
    (executeTool s call k x c).2 = .err .notAllowed ∨
    (executeTool s call k x c).2 = .err .typeError ∨
    (executeTool s call k x c).2 = .err .notFound := by
  rcases executeTool_cases ht x c with h | h | h | ⟨d, hd, _, hid, -, -, hx, -⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · rw [hnot d hd hid] at hx; cases hx

/-- The spec's `Assert: tool definition's name is tool's name` and `Assert: targetOrigin is same
    origin with expectedTargetOrigin` in `executeTool()`. Once `executeTool()` on a `Tool` gets
    past serializing its input, it either rejects with `NotFoundError` or runs the execute steps
    of a registered tool definition with that `Tool`'s tool id and name, in the document the
    `Tool`'s `origin` belongs to, so the call runs exactly the registration `getTools()`
    returned. -/
theorem execute_assert_name {s : State} (h : Invariant s) {c k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[c]?).bind (·[k]?) = some tool) {x : Input} {json : String}
    (hx : x.serialize = some json) (doc : Nat) (hallowed : docAllowed s doc = true) :
    (executeTool s c k x doc).2 = .err .notFound ∨
    ∃ d ∈ s.tools, d.id = tool.id ∧ d.name = tool.name ∧ docOrigin s d.doc = tool.origin ∧
      (executeTool s c k x doc).2 = completionOutcome (invokeExecuteCallback d x json) := by
  have hco : ∀ r, completionOutcome r ≠ .err .notAllowed ∧ completionOutcome r ≠ .err .typeError :=
    fun r => by
      rcases r with e | r
      · cases e <;> simp [completionOutcome, ToolExecutionError.exceptionName]
      · simp [completionOutcome]
  have hne : (executeTool s c k x doc).2 ≠ .err .notAllowed ∧
      (executeTool s c k x doc).2 ≠ .err .typeError := by
    simp only [executeTool, ht, hallowed, hx, Bool.not_true, Bool.false_eq_true, ite_false]
    split
    · simp
    · split
      · simp
      · exact hco _
  rcases executeTool_cases ht x doc with h1 | h1 | h1 | ⟨d, hd, json', hid, hdoc, hx', -, hrun⟩
  · exact absurd h1 hne.1
  · exact absurd h1 hne.2
  · exact .inl h1
  · rw [hx] at hx'
    cases hx'
    obtain ⟨hname, -, horig⟩ := toolObject_named h ht hd hid
    exact .inr ⟨d, hd, hid, hname, by rw [horig, hdoc], hrun⟩

/-! ### Tool ids are never reused

  This is the property the `Tool` interface (spec PR #348) was introduced for: a `Tool` names
  one registration, so once that registration is gone, the `Tool` can never run anything again,
  even if a new tool takes the same name. -/

theorem registerTool_nextId_ge (s : State) (t : ModelContextTool) (sig : Option Nat)
    (exp : List OriginArg) (doc : Nat) : s.nextId ≤ (registerTool s t sig exp doc).1.nextId := by
  cases hc : registerToolChecks s t sig exp doc with
  | some e => rw [registerTool_of_checks_some hc]; exact Nat.le_refl _
  | none => rw [registerTool_of_checks hc]; exact Nat.le_succ _

theorem registerTool_retired {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (t : ModelContextTool) (sig : Option Nat) (exp : List OriginArg) (doc : Nat) :
    n ∉ ids (registerTool s t sig exp doc).1 := by
  cases hc : registerToolChecks s t sig exp doc with
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

theorem getTools_ids (s : State) (fo : List OriginArg) (c : Nat) :
    (getTools s fo c).1.nextId = s.nextId ∧ ids (getTools s fo c).1 = ids s := by
  rcases getTools_state (s := s) (fromOrigins := fo) (c := c) with hs | ⟨_, -, hs⟩ <;>
    rw [hs] <;> exact ⟨rfl, rfl⟩

theorem retired_stays_retired {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (op : Op) : n < (step s op).1.nextId ∧ n ∉ ids (step s op).1 := by
  cases op with
  | register t sig exp doc =>
    exact ⟨Nat.lt_of_lt_of_le hlt (registerTool_nextId_ge s t sig exp doc),
      registerTool_retired n hlt hn t sig exp doc⟩
  | registerAbortSync t sig exp doc =>
    simp only [step, registerAbortSync]
    refine ⟨?_, unregisterBySignal_retired n (registerTool_retired n hlt hn t (some sig) exp doc)
      sig⟩
    rw [unregisterBySignal_nextId]
    exact Nat.lt_of_lt_of_le hlt (registerTool_nextId_ge s t (some sig) exp doc)
  | abort sig =>
    simp only [step]
    exact ⟨by rw [unregisterBySignal_nextId]; exact hlt, unregisterBySignal_retired n hn sig⟩
  | getTools fo doc =>
    simp only [step]
    rw [(getTools_ids s fo doc).1, (getTools_ids s fo doc).2]
    exact ⟨hlt, hn⟩
  | execute c i x doc => simp only [step, executeTool_state]; exact ⟨hlt, hn⟩

theorem retired_stays_retired_run {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) : n ∉ ids (run s ops).1 := by
  induction ops generalizing s with
  | nil => exact hn
  | cons op ops ih =>
    have := retired_stays_retired n hlt hn op
    exact ih this.1 this.2

/-- Executing a `Tool` whose registration is gone fails with `NotFoundError` (or `TypeError`,
    if the input itself cannot be serialized, or `NotAllowedError`, if the caller may not use
    "tools"), whatever the page has done since. -/
theorem stale_tool_not_found {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) (c k : Nat) (x : Input) (name : String) (src : Nat) (org : Origin)
    (doc : Nat) (ht : ((run s ops).1.toolObjects[c]?).bind (·[k]?) = some ⟨n, name, src, org⟩) :
    (executeTool (run s ops).1 c k x doc).2 = .err .notFound ∨
    (executeTool (run s ops).1 c k x doc).2 = .err .typeError ∨
    (executeTool (run s ops).1 c k x doc).2 = .err .notAllowed := by
  have hgone := retired_stays_retired_run n hlt hn ops
  generalize (run s ops).1 = s' at ht hgone ⊢
  rcases executeTool_cases ht x doc with h | h | h | ⟨d, hd, _, hid, -⟩
  · exact .inr (.inr h)
  · exact .inr (.inl h)
  · exact .inl h
  · exact absurd (List.mem_map.mpr ⟨d, hd, hid⟩) hgone

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
/-- info: 'WebMCP.getTools_exposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.getTools_exposed
/-- info: 'WebMCP.getTools_same_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.getTools_same_origin
/-- info: 'WebMCP.getTools_not_from_disallowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.getTools_not_from_disallowed
/-- info: 'WebMCP.executeTool_not_exposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.executeTool_not_exposed
