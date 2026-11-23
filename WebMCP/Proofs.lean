import WebMCP.Model

/-!
# Properties of the model

Each theorem holds for every state, or every state satisfying `Invariant` (so every reachable
one). Three of them discharge an `Assert` step of the spec, showing it can never fail, which is
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

/-! ### How states evolve

  Every operation only adds tools under fresh tool ids, removes tools, and adds `Tool` objects:
  `Evolves s t`. The frame tree never changes. -/

/-- `t` is `s` with tools added under fresh ids, tools removed, or `Tool` objects added. -/
structure Evolves (s t : State) : Prop where
  /-- The frame tree is the same. -/
  docs : t.docs = s.docs
  /-- Tool ids are only ever issued. -/
  nextId : s.nextId ≤ t.nextId
  /-- Every tool of `t` was already in `s`, or has an id `s` hadn't issued. -/
  tools : ∀ d ∈ t.tools, d ∈ s.tools ∨ s.nextId ≤ d.id

theorem Evolves.refl (s : State) : Evolves s s :=
  ⟨rfl, Nat.le_refl _, fun _ hd => .inl hd⟩

theorem Evolves.trans {s t u : State} (h1 : Evolves s t) (h2 : Evolves t u) : Evolves s u := by
  refine ⟨h2.docs.trans h1.docs, Nat.le_trans h1.nextId h2.nextId, fun d hd => ?_⟩
  rcases h2.tools d hd with hd | hle
  · exact h1.tools d hd
  · exact .inr (Nat.le_trans h1.nextId hle)

theorem Evolves.docOrigin {s t : State} (h : Evolves s t) (d : Nat) :
    WebMCP.docOrigin t d = WebMCP.docOrigin s d := by
  simp [WebMCP.docOrigin, h.docs]

theorem evolves_toolObjects (s : State) (l : List (List ToolObject)) :
    Evolves s { s with toolObjects := l } :=
  ⟨rfl, Nat.le_refl _, fun _ hd => .inl hd⟩

theorem addTool_evolves (s : State) (t : ModelContextTool) (sig : Option Nat)
    (exp : List OriginArg) (doc : Nat) : Evolves s (addTool s t sig exp doc) := by
  refine ⟨rfl, Nat.le_succ _, fun d hd => ?_⟩
  rcases mem_addTool.mp hd with hd | rfl
  · exact .inl hd
  · exact .inr (Nat.le_refl _)

theorem registerTool_evolves (s : State) (t : ModelContextTool) (sig : Option Nat)
    (exp : List OriginArg) (doc : Nat) : Evolves s (registerTool s t sig exp doc).1 := by
  cases hc : registerToolChecks s t sig exp doc with
  | some e => rw [registerTool_of_checks_some hc]; exact .refl s
  | none => rw [registerTool_of_checks hc]; exact addTool_evolves s t sig exp doc

theorem unregisterBySignal_evolves (s : State) (sig : Nat) :
    Evolves s (unregisterBySignal s sig).1 := by
  by_cases hn : sig ∈ s.aborted
  · rw [unregisterBySignal_of_aborted hn]; exact .refl s
  · rw [unregisterBySignal_of_fresh hn]
    exact ⟨rfl, Nat.le_refl _, fun d hd => .inl (mem_filter_signal.mp hd).1⟩

theorem getTools_evolves (s : State) (fo : List OriginArg) (c : Nat) :
    Evolves s (getTools s fo c).1 := by
  rcases getTools_state (s := s) (fromOrigins := fo) (c := c) with hs | ⟨_, -, hs⟩ <;> rw [hs] <;>
    exact evolves_toolObjects s _

theorem callbackEffect_spec {s : State} (h : Invariant s) (d : ToolDef) (x : Input) :
    Invariant (callbackEffect s d x) ∧ Evolves s (callbackEffect s d x) := by
  unfold callbackEffect
  split
  · exact ⟨unregisterBySignal_invariant h _, unregisterBySignal_evolves s _⟩
  · exact ⟨h, .refl s⟩

theorem toolExecuteEffect_spec {s : State} (h : Invariant s) (doc id : Nat) (x : Input) :
    Invariant (toolExecuteEffect s doc id x) ∧ Evolves s (toolExecuteEffect s doc id x) := by
  unfold toolExecuteEffect
  split
  · exact ⟨h, .refl s⟩
  · exact callbackEffect_spec h _ x

theorem executeTool_spec {s : State} (h : Invariant s) (c i : Nat) (x : Input) (doc : Nat) :
    Invariant (executeTool s c i x doc).1 ∧ Evolves s (executeTool s c i x doc).1 := by
  unfold executeTool
  repeat' split
  all_goals first | exact ⟨h, .refl s⟩ | exact toolExecuteEffect_spec h _ _ x

/-! ### `Tool` objects read from an earlier state -/

/-- What the invariant asks of a `Tool` object held in state `t`. -/
def ObjOK (t : State) (o : ToolObject) : Prop :=
  o.id < t.nextId ∧ (∀ d ∈ t.tools, d.id = o.id → d.name = o.name ∧ d.doc = o.source) ∧
    o.origin = docOrigin t o.source

theorem appendObjects_invariant {t : State} (h : Invariant t) {L : List (List ToolObject)}
    (hL : ∀ objs ∈ L, ∀ o ∈ objs, ObjOK t o) :
    Invariant { t with toolObjects := t.toolObjects ++ L } := by
  constructor
  · exact h.names_unique
  · exact h.id_determines
  · exact h.ids_issued
  · intro ts hts o ho
    rcases List.mem_append.mp hts with hts | hts
    · exact h.toolObjects_issued ts hts o ho
    · exact (hL ts hts o ho).1
  · intro ts hts o ho d hd heq
    rcases List.mem_append.mp hts with hts | hts
    · exact h.toolObjects_named ts hts o ho d hd heq
    · exact (hL ts hts o ho).2.1 d hd heq
  · intro ts hts o ho
    rcases List.mem_append.mp hts with hts | hts
    · exact h.toolObjects_origin ts hts o ho
    · exact (hL ts hts o ho).2.2
  · exact h.tools_allowed
  · exact h.names_valid
  · exact h.descriptions
  · exact h.signals_live
  · exact h.abortSteps_target

/-- The `Tool` objects a `getTools()` creates from state `s` stay valid in any state `s`
    evolves to: tool ids are never reused, so a later tool with the same id is the same one. -/
theorem getTools_objects_ok {s t : State} (hs : Invariant s) (he : Evolves s t)
    (fo : List OriginArg) (c : Nat) :
    ∀ o ∈ (getTools s fo c).1.toolObjects.getLastD [], ObjOK t o := by
  intro o ho
  rcases getTools_state (s := s) (fromOrigins := fo) (c := c) with hs' | ⟨fo', -, hs'⟩ <;>
    rw [hs'] at ho <;> simp only [List.getLastD_concat] at ho
  · cases ho
  obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp ho
  have hd0 := (mem_discover.mp (mem_sortTools.mp hd0)).1
  refine ⟨Nat.lt_of_lt_of_le (hs.ids_issued d0 hd0) he.nextId, fun d hd heq => ?_, ?_⟩
  · rcases he.tools d hd with hd | hle
    · have := hs.id_determines d hd d0 hd0 heq
      subst this; exact ⟨rfl, rfl⟩
    · have heq' : d.id = d0.id := heq
      rw [heq'] at hle
      exact absurd hle (Nat.not_le.mpr (hs.ids_issued d0 hd0))
  · simp [ToolDef.object, he.docOrigin]

/-! ### `Op.concurrent` -/

theorem syncAction_spec {s : State} (h : Invariant s) (doc : Nat) (ps : List Pending)
    (a : Action) :
    Invariant (syncAction doc s ps a).1 ∧ Evolves s (syncAction doc s ps a).1 := by
  cases a with
  | register t sig exp =>
    simp only [syncAction]
    cases hc : registerToolChecks s t sig exp doc with
    | some e => exact ⟨h, .refl s⟩
    | none => exact ⟨addTool_invariant h hc, addTool_evolves s t sig exp doc⟩
  | abort g => exact ⟨unregisterBySignal_invariant h g, unregisterBySignal_evolves s g⟩
  | getTools fo =>
    simp only [syncAction]
    repeat' split
    all_goals exact ⟨h, .refl s⟩
  | execute c k x sg =>
    simp only [syncAction]
    repeat' split
    all_goals exact ⟨h, .refl s⟩
  | cancel k => exact ⟨h, .refl s⟩

/-- The script of an `Op.concurrent` keeps the invariant, and every state a `getTools()` may
    read during it evolves to the state at its end. -/
theorem syncPhase_spec {doc : Nat} (as : List Action) :
    ∀ {s : State} {ps : List Pending} {hist : List State}, Invariant s →
      Invariant (syncPhase doc s ps hist as).1 ∧ Evolves s (syncPhase doc s ps hist as).1 ∧
      ∀ st ∈ (syncPhase doc s ps hist as).2.2, st ∈ hist ∨
        (Invariant st ∧ Evolves st (syncPhase doc s ps hist as).1) := by
  induction as with
  | nil =>
    intro s ps hist h
    simp only [syncPhase, List.mem_append, List.mem_singleton]
    refine ⟨h, .refl s, fun st hst => ?_⟩
    rcases hst with hst | rfl
    · exact .inl hst
    · exact .inr ⟨h, .refl _⟩
  | cons a as ih =>
    intro s ps hist h
    obtain ⟨hi, he⟩ := syncAction_spec h doc ps a
    rcases hsa : syncAction doc s ps a with ⟨s', p, ps'⟩
    rw [hsa] at hi he
    simp only [syncPhase, hsa]
    obtain ⟨hi', he', hh⟩ := ih (ps := ps' ++ [p.since hist.length]) (hist := hist ++ [s]) hi
    refine ⟨hi', he.trans he', fun st hst => ?_⟩
    rcases hh st hst with hst | hst
    · rcases List.mem_append.mp hst with hst | hst
      · exact .inl hst
      · simp only [List.mem_singleton] at hst
        subst hst
        exact .inr ⟨h, he.trans he'⟩
    · exact .inr hst

theorem asyncStep_spec {s : State} (h : Invariant s) (doc : Nat) (p : Pending) :
    Invariant (asyncStep doc s p).1 ∧ Evolves s (asyncStep doc s p).1 := by
  cases p with
  | executing tool x json c cc =>
    simp only [asyncStep]
    cases hl : lookup s tool.source tool.id with
    | none => exact ⟨h, .refl s⟩
    | some d =>
      simp only []
      split
      · exact ⟨h, .refl s⟩
      · exact callbackEffect_spec h d x
  | _ => exact ⟨h, .refl s⟩

/-- The tool executions of an `Op.concurrent` keep the invariant, and every state after one of
    them evolves to the state at the end. -/
theorem asyncPhase_spec {doc : Nat} {ps : List Pending} (order : List Nat) :
    ∀ {s : State}, Invariant s →
      Invariant (asyncPhase doc ps s order).1 ∧ Evolves s (asyncPhase doc ps s order).1 ∧
      ∀ st ∈ (asyncPhase doc ps s order).2.2.1,
        Invariant st ∧ Evolves st (asyncPhase doc ps s order).1 := by
  induction order with
  | nil => intro s h; exact ⟨h, .refl s, by simp [asyncPhase]⟩
  | cons i is ih =>
    intro s h
    obtain ⟨hi, he⟩ := asyncStep_spec h doc (ps[i]?.getD .invalid)
    rcases has : asyncStep doc s (ps[i]?.getD .invalid) with ⟨s', o, g⟩
    rw [has] at hi he
    simp only at hi he
    obtain ⟨hi', he', hh⟩ := ih hi
    simp only [asyncPhase, has, List.mem_cons]
    refine ⟨hi', he.trans he', fun st hst => ?_⟩
    rcases hst with rfl | hst
    · exact ⟨hi, he'⟩
    · exact hh st hst

theorem mem_choices {α : Type} {L : List (List α)} {picked : List α} (h : picked ∈ choices L)
    {x : α} (hx : x ∈ picked) : ∃ l ∈ L, x ∈ l := by
  induction L generalizing picked with
  | nil => simp [choices] at h; subst h; cases hx
  | cons c cs ih =>
    simp only [choices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨y, hy, rest, hrest, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨c, List.mem_cons_self, hy⟩
    · obtain ⟨l, hl, hxl⟩ := ih hrest hx
      exact ⟨l, List.mem_cons_of_mem _ hl, hxl⟩

/-- The `Tool` objects an `Op.concurrent` call can return: none, or what a `getTools()` would
    create from one of the states it may read. -/
theorem callChoices_objs {doc : Nat} {hist ahist : List State} {ex : List (Nat × Outcome)}
    {gs : List Nat} {i : Nat} {p : Pending} {x : Outcome × Option (List ToolObject)}
    (hx : x ∈ callChoices doc hist ahist ex gs i p) {objs : List ToolObject}
    (hobjs : x.2 = some objs) :
    objs = [] ∨ ∃ st, (st ∈ hist ∨ st ∈ ahist) ∧
      ∃ fo, objs = (getTools st fo doc).1.toolObjects.getLastD [] := by
  cases p with
  | settled o => simp [callChoices] at hx; subst hx; cases hobjs
  | readFailed e => simp [callChoices] at hx; subst hx; cases hobjs; exact .inl rfl
  | registered sig ab =>
    simp only [callChoices] at hx
    repeat' split at hx
    all_goals simp at hx
    all_goals rcases hx with rfl | rfl <;> cases hobjs
  | reading fo since =>
    simp only [callChoices, List.mem_map] at hx
    obtain ⟨st, hst, rfl⟩ := hx
    cases hobjs
    rcases List.mem_append.mp hst with hst | hst
    · exact .inr ⟨st, .inl (List.mem_of_mem_drop hst), fo, rfl⟩
    · exact .inr ⟨st, .inr hst, fo, rfl⟩
  | executing => simp [callChoices] at hx; subst hx; cases hobjs
  | invalid => simp [callChoices] at hx; subst hx; cases hobjs

/-- Every branch of an `Op.concurrent` keeps the invariant. -/
theorem concurrent_spec {s : State} (h : Invariant s) (as : List Action) (doc : Nat) :
    ∀ p ∈ concurrent s as doc, Invariant p.1 ∧ Evolves s p.1 := by
  intro p hp
  unfold concurrent at hp
  obtain ⟨hiE, heE, hhist⟩ := syncPhase_spec (doc := doc) (ps := []) (hist := []) as h
  rcases hsync : syncPhase doc s [] [] as with ⟨sEnd, ps, hist⟩
  rw [hsync] at hiE heE hhist
  simp only [hsync] at hp
  split at hp
  · simp only [List.mem_singleton] at hp; subst hp; exact ⟨h, .refl s⟩
  simp only [List.mem_flatMap, List.mem_map] at hp
  obtain ⟨order, -, picked, hpicked, rfl⟩ := hp
  obtain ⟨hiA, heA, hahist⟩ := asyncPhase_spec (doc := doc) (ps := ps) order hiE
  rcases hasync : asyncPhase doc ps sEnd order with ⟨sA, ex, ahist, gs⟩
  rw [hasync] at hiA heA hahist
  simp only [hasync] at hpicked ⊢
  refine ⟨appendObjects_invariant hiA fun objs hobjs o ho => ?_,
    (heE.trans heA).trans (evolves_toolObjects _ _)⟩
  obtain ⟨x, hx, hxo⟩ := List.mem_filterMap.mp hobjs
  obtain ⟨l, hl, hxl⟩ := mem_choices hpicked hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hl
  rcases callChoices_objs hxl hxo with rfl | ⟨st, hst, fo, rfl⟩
  · cases ho
  rcases hst with hst | hst
  · rcases hhist st hst with hst | ⟨his, hes⟩
    · cases hst
    · exact getTools_objects_ok his (hes.trans heA) fo doc o ho
  · obtain ⟨his, hes⟩ := hahist st hst
    exact getTools_objects_ok his hes fo doc o ho

theorem registerAbortSync_invariant {s : State} (h : Invariant s) (t : ModelContextTool)
    (sig : Nat) (exp : List OriginArg) (doc : Nat) :
    Invariant (registerAbortSync s t sig exp doc).1 :=
  unregisterBySignal_invariant (registerTool_invariant h t (some sig) exp doc) sig

/-- Every allowed outcome of an operation leaves a state where the invariant holds, and that
    state evolved from the one before. -/
theorem step_spec {s : State} (h : Invariant s) (op : Op) :
    ∀ p ∈ step s op, Invariant p.1 ∧ Evolves s p.1 := by
  cases op with
  | concurrent as doc => exact concurrent_spec h as doc
  | _ =>
    intro p hp
    simp only [step, List.mem_singleton] at hp
    subst hp
    first
      | exact ⟨registerTool_invariant h _ _ _ _, registerTool_evolves s _ _ _ _⟩
      | exact ⟨registerAbortSync_invariant h _ _ _ _,
          (registerTool_evolves s _ _ _ _).trans (unregisterBySignal_evolves _ _)⟩
      | exact ⟨unregisterBySignal_invariant h _, unregisterBySignal_evolves s _⟩
      | exact ⟨getTools_invariant h _ _, getTools_evolves s _ _⟩
      | exact executeTool_spec h _ _ _ _

theorem step_invariant {s : State} (h : Invariant s) (op : Op) :
    ∀ p ∈ step s op, Invariant p.1 :=
  fun p hp => (step_spec h op p hp).1

/-- Every operation but `Op.concurrent` has exactly one outcome. -/
theorem step_deterministic (s : State) (op : Op) (hop : ∀ as doc, op ≠ .concurrent as doc) :
    ∃ p, step s op = [p] := by
  cases op with
  | concurrent as doc => exact absurd rfl (hop as doc)
  | _ => exact ⟨_, rfl⟩

/-- The invariant holds after any sequence of operations, in every branch, and every branch's
    state evolved from the first. -/
theorem run_spec (ops : List Op) :
    ∀ {s : State}, Invariant s → ∀ p ∈ run s ops, Invariant p.1 ∧ Evolves s p.1 := by
  induction ops with
  | nil => intro s h p hp; simp [run] at hp; subst hp; exact ⟨h, .refl s⟩
  | cons op ops ih =>
    intro s h p hp
    simp only [run, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, r, hr, rfl⟩ := hp
    obtain ⟨hiq, heq⟩ := step_spec h op q hq
    obtain ⟨hir, her⟩ := ih hiq r hr
    exact ⟨hir, heq.trans her⟩

/-- The invariant holds after any sequence of operations, in every branch. -/
theorem run_invariant {s : State} (h : Invariant s) (ops : List Op) :
    ∀ p ∈ run s ops, Invariant p.1 :=
  fun p hp => (run_spec ops h p hp).1

/-- The invariant holds in every reachable state. -/
theorem reachable_invariant (ops : List Op) : ∀ p ∈ run {} ops, Invariant p.1 :=
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

/-! ### The exposure check for calls in flight

  `executeTool_not_exposed` is about an awaited call. An `executeTool()` started inside an
  `Op.concurrent` reaches its queued "tool execute steps" (`asyncStep`) later, after the rest of
  the script and maybe other tools' callbacks, so the theorems below follow its `Tool` from the
  call to that task. -/

/-- The queued "tool execute steps" of a `Tool` whose registration is not exposed to the
    caller's origin leave the page as it was, abort no signal, and settle with `NotFoundError`
    (or `AbortError`, if the call was cancelled first): the callback never runs. This holds in
    any state the page has evolved to since the `Tool` was created. -/
theorem asyncStep_not_exposed {s st : State} (he : Evolves s st) {doc : Nat} {tool : ToolObject}
    (hlt : tool.id < s.nextId)
    (hnot : ∀ d ∈ s.tools, d.id = tool.id →
      toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s doc) = false)
    (x : Input) (json : String) (c cc : Bool) :
    asyncStep doc st (.executing tool x json c cc) =
      (st, some (if c then .err .abort else .err .notFound), none) := by
  simp only [asyncStep]
  cases hl : lookup st tool.source tool.id with
  | none => rfl
  | some d =>
    obtain ⟨hd, hdoc, hid⟩ := mem_lookup hl
    have hd' : d ∈ s.tools := by
      rcases he.tools d hd with hd' | hle
      · exact hd'
      · exact absurd (hid ▸ hle) (Nat.not_le.mpr hlt)
    have hx := hnot d hd' hid
    rw [hdoc, ← he.docOrigin, ← he.docOrigin] at hx
    simp [hx]

/-- A call of an `Op.concurrent` that cannot run the callback of `tool`'s registration through
    another `Tool`: it settled before reaching the tool, or it waits to run `tool` itself. -/
def NoRun (tool : ToolObject) : Pending → Prop
  | .settled o => o = .err .notAllowed ∨ o = .err .typeError ∨ o = .err .abort
  | .invalid => True
  | .executing t .. => t = tool
  | _ => False

theorem NoRun.since {tool : ToolObject} {p : Pending} (h : NoRun tool p) (n : Nat) :
    NoRun tool (p.since n) := by
  cases p <;> simp_all [Pending.since, NoRun]

theorem syncAction_toolObjects (doc : Nat) (s : State) (ps : List Pending) (a : Action) :
    (syncAction doc s ps a).1.toolObjects = s.toolObjects := by
  cases a with
  | register t sig exp =>
    simp only [syncAction]; split <;> rfl
  | abort g => simp only [syncAction, unregisterBySignal]; split <;> rfl
  | getTools fo => simp only [syncAction]; repeat' split
                   all_goals rfl
  | execute c k x sg => simp only [syncAction]; repeat' split
                        all_goals rfl
  | cancel k => rfl

/-- The synchronous part of an action changes the earlier calls only by marking a registration
    aborted or an execution cancelled, so a call that couldn't run another tool still can't. -/
theorem syncAction_keeps (tool : ToolObject) (doc : Nat) (s : State) (ps : List Pending)
    (a : Action) :
    (syncAction doc s ps a).2.2.length = ps.length ∧
    ∀ (j : Nat) (p : Pending), (syncAction doc s ps a).2.2[j]? = some p →
      ∃ q, ps[j]? = some q ∧ (NoRun tool q → NoRun tool p) := by
  cases a with
  | register t sig exp =>
    simp only [syncAction]; split <;> exact ⟨rfl, fun j p hp => ⟨p, hp, id⟩⟩
  | abort g =>
    simp only [syncAction, List.length_map, List.getElem?_map, true_and]
    intro j p hp
    cases hq : ps[j]? with
    | none => simp [hq] at hp
    | some q =>
      simp only [hq, Option.map_some, Option.some.injEq] at hp
      refine ⟨q, rfl, fun hn => ?_⟩
      subst hp
      cases q <;> simp_all [NoRun]
  | getTools fo =>
    simp only [syncAction]; repeat' split
    all_goals exact ⟨rfl, fun j p hp => ⟨p, hp, id⟩⟩
  | execute c k x sg =>
    simp only [syncAction]; repeat' split
    all_goals exact ⟨rfl, fun j p hp => ⟨p, hp, id⟩⟩
  | cancel k =>
    simp only [syncAction, List.length_mapIdx, List.getElem?_mapIdx, true_and]
    intro j p hp
    cases hq : ps[j]? with
    | none => simp [hq] at hp
    | some q =>
      simp only [hq, Option.map_some, Option.some.injEq] at hp
      refine ⟨q, rfl, fun hn => ?_⟩
      subst hp
      cases q with
      | executing t x json c cc =>
        simp only [NoRun] at hn
        cases c <;> cases cc <;> by_cases hjk : (j == k) = true <;> simp [hjk, NoRun, hn]
      | _ => simp_all [NoRun]

/-- `executeTool(tool)` started in a script can't run another tool's callback. -/
theorem syncAction_execute_noRun {s : State} {call k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) (doc : Nat) (ps : List Pending)
    (x : Input) (sg : ExecSignal) :
    NoRun tool (syncAction doc s ps (.execute call k x sg)).2.1 := by
  simp only [syncAction, ht]
  repeat' split
  all_goals simp [NoRun]

/-- Every `executeTool(tool)` of the script ends it unable to run another tool's callback. -/
theorem syncPhase_noRun {doc : Nat} {T : List (List ToolObject)} {call k : Nat}
    {tool : ToolObject} (ht : (T[call]?).bind (·[k]?) = some tool) (as0 : List Action) :
    ∀ (as pre : List Action) (s : State) (ps : List Pending) (hist : List State),
      s.toolObjects = T → as0 = pre ++ as → pre.length = ps.length →
      (∀ (j : Nat) (p : Pending) (x : Input) (sg : ExecSignal),
        as0[j]? = some (Action.execute call k x sg) → ps[j]? = some p → NoRun tool p) →
      ∀ (j : Nat) (p : Pending) (x : Input) (sg : ExecSignal),
        as0[j]? = some (Action.execute call k x sg) →
        (syncPhase doc s ps hist as).2.1[j]? = some p → NoRun tool p := by
  intro as
  induction as with
  | nil => intro pre s ps hist _ _ _ hps; simpa [syncPhase] using hps
  | cons a as ih =>
    intro pre s ps hist hT has hlen hps
    obtain ⟨hlen', hkeep⟩ := syncAction_keeps tool doc s ps a
    rcases hsa : syncAction doc s ps a with ⟨s', p, ps'⟩
    rw [hsa] at hlen' hkeep
    simp only at hlen' hkeep
    have hT' : s'.toolObjects = T := by
      have := syncAction_toolObjects doc s ps a; rw [hsa] at this; exact this.trans hT
    simp only [syncPhase, hsa]
    refine ih (pre ++ [a]) s' (ps' ++ [p.since hist.length]) (hist ++ [s]) hT'
      (by simp [has]) (by simp [hlen, hlen']) ?_
    intro j q x sg hj hq
    by_cases hlt : j < ps'.length
    · rw [List.getElem?_append_left hlt] at hq
      obtain ⟨q0, hq0, himp⟩ := hkeep j q hq
      exact himp (hps j q0 x sg hj hq0)
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hq
      cases hd : j - ps'.length with
      | succ n => simp [hd] at hq
      | zero =>
        simp only [hd, List.getElem?_cons_zero, Option.some.injEq] at hq
        subst hq
        have hj' : j = pre.length := by omega
        have ha : a = .execute call k x sg := by
          rw [has, hj', List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hj
          simpa using hj
        subst ha
        have := syncAction_execute_noRun (hT ▸ ht) doc ps x sg
        rw [hsa] at this
        exact this.since _

/-- The tasks of an `Op.concurrent` settle an `executeTool(tool)` whose registration is not
    exposed to the caller's origin with `NotFoundError` or `AbortError`. -/
theorem asyncPhase_not_exposed {s : State} {doc : Nat} {tool : ToolObject}
    (hlt : tool.id < s.nextId)
    (hnot : ∀ d ∈ s.tools, d.id = tool.id →
      toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s doc) = false)
    {ps : List Pending} (order : List Nat) :
    ∀ st, Invariant st → Evolves s st → ∀ j o, (j, o) ∈ (asyncPhase doc ps st order).2.1 →
      ∀ x json c cc, ps[j]? = some (.executing tool x json c cc) →
        o = .err .abort ∨ o = .err .notFound := by
  induction order with
  | nil => intro st _ _ j o hm; simp [asyncPhase] at hm
  | cons i is ih =>
    intro st hi he j o hm x json c cc hj
    obtain ⟨hi', he'⟩ := asyncStep_spec hi doc (ps[i]?.getD .invalid)
    rcases has : asyncStep doc st (ps[i]?.getD .invalid) with ⟨s', o', g⟩
    rw [has] at hi' he'
    simp only [asyncPhase, has, List.mem_append] at hm
    rcases hm with hm | hm
    · cases o' with
      | none => simp at hm
      | some o'' =>
        simp only [Option.map_some, Option.getD_some, List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        rw [hj, Option.getD_some, asyncStep_not_exposed he hlt hnot] at has
        simp only [Prod.mk.injEq, Option.some.injEq] at has
        obtain ⟨-, rfl, -⟩ := has
        split <;> simp
    · exact ih s' hi' (he.trans he') j o hm x json c cc hj

/-- Every waiting `executeTool()` whose index is in `order` gets an outcome. -/
theorem asyncPhase_settles {doc : Nat} {ps : List Pending} (order : List Nat) :
    ∀ st i, i ∈ order → ∀ tool x json c cc, ps[i]? = some (.executing tool x json c cc) →
      ∃ o, (i, o) ∈ (asyncPhase doc ps st order).2.1 := by
  induction order with
  | nil => intro st i hi; cases hi
  | cons j is ih =>
    intro st i hi tool x json c cc hps
    rcases has : asyncStep doc st (ps[j]?.getD .invalid) with ⟨s', o', g⟩
    simp only [asyncPhase, has, List.mem_append]
    by_cases hij : i = j
    · subst hij
      rw [hps, Option.getD_some] at has
      simp only [asyncStep] at has
      cases o' with
      | none => simp at has
      | some o'' => exact ⟨o'', .inl (by simp)⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact absurd rfl hij
      · obtain ⟨o, ho⟩ := ih s' i hi tool x json c cc hps
        exact ⟨o, .inr ho⟩

theorem mem_insertEverywhere {x : Nat} {l o : List Nat} (h : o ∈ insertEverywhere x l) :
    x ∈ o ∧ ∀ y ∈ l, y ∈ o := by
  induction l generalizing o with
  | nil => simp [insertEverywhere] at h; subst h; simp
  | cons y ys ih =>
    simp only [insertEverywhere, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨o', ho', rfl⟩
    · exact ⟨List.mem_cons_self, fun z hz => List.mem_cons_of_mem _ hz⟩
    · obtain ⟨hx, hys⟩ := ih ho'
      refine ⟨List.mem_cons_of_mem _ hx, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hys z hz)

theorem mem_orders {l o : List Nat} (h : o ∈ orders l) : ∀ y ∈ l, y ∈ o := by
  induction l generalizing o with
  | nil => intro y hy; cases hy
  | cons x xs ih =>
    simp only [orders, List.mem_flatMap] at h
    obtain ⟨o', ho', ho⟩ := h
    obtain ⟨hx, hxs⟩ := mem_insertEverywhere ho
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hxs y (ih ho' y hy)

theorem lookup_of_mem {l : List (Nat × Outcome)} {i : Nat} {o : Outcome} (h : (i, o) ∈ l) :
    ∃ o', l.lookup i = some o' ∧ (i, o') ∈ l := by
  induction l with
  | nil => cases h
  | cons e es ih =>
    rcases e with ⟨k, b⟩
    by_cases hk : i = k
    · subst hk; exact ⟨b, by simp [List.lookup], List.mem_cons_self⟩
    · have hne : (i == k) = false := by simpa using hk
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1 hk
      · obtain ⟨o', ho', hm⟩ := ih h
        exact ⟨o', by simp [List.lookup, hne, ho'], List.mem_cons_of_mem _ hm⟩

theorem choices_getElem? {α : Type} {L : List (List α)} {picked : List α}
    (h : picked ∈ choices L) {i : Nat} {x : α} (hx : picked[i]? = some x) :
    ∃ l, L[i]? = some l ∧ x ∈ l := by
  induction L generalizing picked i with
  | nil => simp [choices] at h; subst h; simp at hx
  | cons c cs ih =>
    simp only [choices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨y, hy, rest, hrest, rfl⟩ := h
    cases i with
    | zero => simp at hx; subst hx; exact ⟨c, rfl, hy⟩
    | succ n => simpa using ih hrest (by simpa using hx)

/-- **A tool never runs for an origin it is not exposed to, even with calls in flight.** If the
    registration a `Tool` identifies is not exposed to the origin of document `doc`, then an
    `executeTool()` on it started from `doc`'s script in an `Op.concurrent`, together with any
    other calls (registrations, aborts, `getTools()`, other executions, cancellations), settles
    in every allowed order with `NotAllowedError`, `TypeError`, `AbortError` or `NotFoundError`.
    Its queued tool execute steps leave the page unchanged (`asyncStep_not_exposed`), so the
    tool's `execute` callback never runs there. -/
theorem concurrent_not_exposed {s : State} (h : Invariant s) {call k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) (doc : Nat)
    (hnot : ∀ d ∈ s.tools, d.id = tool.id →
      toolIsExposed (docOrigin s d.doc) d.exposedOrigins (docOrigin s doc) = false)
    (as : List Action) {i : Nat} {x : Input} {sg : ExecSignal}
    (hi : as[i]? = some (.execute call k x sg)) :
    ∀ p ∈ concurrent s as doc, ∀ os, p.2 = .all os → ∀ o, os[i]? = some o →
      o = .err .notAllowed ∨ o = .err .typeError ∨ o = .err .abort ∨ o = .err .notFound := by
  have hlt : tool.id < s.nextId := by
    cases hc : s.toolObjects[call]? with
    | none => simp [hc] at ht
    | some ts =>
      simp only [hc, Option.bind_some] at ht
      exact h.toolObjects_issued ts (List.mem_of_getElem? hc) tool (List.mem_of_getElem? ht)
  intro p hp os hos o ho
  obtain ⟨hiE, -, -⟩ := syncPhase_spec (doc := doc) (ps := []) (hist := []) as h
  have hnr := syncPhase_noRun (doc := doc) ht as as [] s [] [] rfl rfl rfl (by simp)
  unfold concurrent at hp
  rcases hsync : syncPhase doc s [] [] as with ⟨sEnd, ps, hist⟩
  rw [hsync] at hiE hnr
  simp only [hsync] at hp
  split at hp
  · simp only [List.mem_singleton] at hp; subst hp; cases hos
  rename_i hnoinv
  simp only [List.mem_flatMap, List.mem_map] at hp
  obtain ⟨order, horder, picked, hpicked, rfl⟩ := hp
  simp only [Outcome.all.injEq] at hos
  subst hos
  rw [List.getElem?_map] at ho
  cases hpi : picked[i]? with
  | none => simp [hpi] at ho
  | some pr =>
    simp only [hpi, Option.map_some, Option.some.injEq] at ho
    subst ho
    obtain ⟨l, hl, hpr⟩ := choices_getElem? hpicked hpi
    rw [List.getElem?_map] at hl
    have hilt : i < ps.length := by
      rcases Nat.lt_or_ge i ps.length with hilt | hge
      · exact hilt
      · rw [List.getElem?_eq_none (by simpa using hge)] at hl
        simp at hl
    rw [List.getElem?_range hilt] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    have hps : ps[i]? = some ps[i] := List.getElem?_eq_getElem hilt
    have hq := hnr i ps[i] x sg hi hps
    rw [hps, Option.getD_some] at hpr
    generalize ps[i] = q at hq hpr hps
    cases q with
    | settled o' =>
      simp only [callChoices, List.mem_singleton] at hpr
      subst hpr
      rcases hq with hq | hq | hq <;> simp [hq]
    | readFailed | registered | reading => cases hq
    | invalid =>
      exact absurd (List.any_eq_true.mpr ⟨_, List.mem_of_getElem? hps, rfl⟩) hnoinv
    | executing t x' json c cc =>
      simp only [NoRun] at hq
      subst hq
      simp only [callChoices, List.mem_singleton] at hpr
      subst hpr
      have hiw : i ∈ (List.range ps.length).filter fun j =>
          match ps[j]? with | some (.executing ..) => true | _ => false := by
        exact List.mem_filter.mpr ⟨List.mem_range.mpr hilt, by simp [hps]⟩
      obtain ⟨o1, ho1⟩ := asyncPhase_settles (doc := doc) order sEnd i (mem_orders horder i hiw)
        t x' json c cc hps
      obtain ⟨o', hlk, hm⟩ := lookup_of_mem ho1
      simp only [hlk, Option.getD_some]
      have heE : Evolves s sEnd := by
        have := (syncPhase_spec (doc := doc) (ps := []) (hist := []) as h).2.1
        rw [hsync] at this; exact this
      rcases asyncPhase_not_exposed hlt hnot order sEnd hiE heE i o' hm x' json c cc hps with
        hr | hr <;> simp [hr]

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

theorem unregisterBySignal_nextId (s : State) (sig : Nat) :
    (unregisterBySignal s sig).1.nextId = s.nextId := by
  unfold unregisterBySignal; split <;> rfl

/-- A tool id that was issued and is no longer registered stays that way. -/
theorem Evolves.retired {s t : State} (he : Evolves s t) {n : Nat} (hlt : n < s.nextId)
    (hn : n ∉ ids s) : n ∉ ids t := by
  simp only [ids, List.mem_map, not_exists, not_and] at hn ⊢
  intro d hd heq
  rcases he.tools d hd with hd | hle
  · exact hn d hd heq
  · exact absurd (heq ▸ hle) (Nat.not_le.mpr hlt)

/-- Executing a `Tool` whose registration is gone fails with `NotFoundError` (or `TypeError`,
    if the input itself cannot be serialized, or `NotAllowedError`, if the caller may not use
    "tools"), whatever the page has done since, in every branch. -/
theorem stale_tool_not_found {s : State} (hs : Invariant s) (n : Nat) (hlt : n < s.nextId)
    (hn : n ∉ ids s) (ops : List Op) (p : State × List Outcome) (hp : p ∈ run s ops)
    (c k : Nat) (x : Input) (name : String) (src : Nat) (org : Origin) (doc : Nat)
    (ht : (p.1.toolObjects[c]?).bind (·[k]?) = some ⟨n, name, src, org⟩) :
    (executeTool p.1 c k x doc).2 = .err .notFound ∨
    (executeTool p.1 c k x doc).2 = .err .typeError ∨
    (executeTool p.1 c k x doc).2 = .err .notAllowed := by
  have hgone := (run_spec ops hs p hp).2.retired hlt hn
  rcases executeTool_cases ht x doc with h | h | h | ⟨d, hd, _, hid, -⟩
  · exact .inr (.inr h)
  · exact .inr (.inl h)
  · exact .inl h
  · exact absurd (List.mem_map.mpr ⟨d, hd, hid⟩) hgone

/-! ### Races

  The spec's notes on what happens when a tool is unregistered while a call that uses it is in
  flight. -/

theorem range_two : List.range 2 = [0, 1] := rfl
theorem range_three : List.range 3 = [0, 1, 2] := rfl

theorem lookup_none {s : State} {doc id : Nat} (h : ∀ d ∈ s.tools, d.id ≠ id) :
    lookup s doc id = none := by
  rw [lookup, List.find?_eq_none]
  intro d hd heq
  simp only [Bool.and_eq_true, beq_iff_eq] at heq
  exact h d hd heq.2

/-- **Unregistration racing execution** (the note in "tool execute steps", and its example
    `unregistration-execution-race`). Start `executeTool()` on a `Tool`, then, in the same script,
    abort the signal its tool was registered with and register a new tool, under any name (such
    as the old one). In every allowed order, the `executeTool()` call does not run anything: it
    rejects with `NotFoundError` (or before that, with `NotAllowedError` or `TypeError`), and
    the other two calls settle as they would have alone. -/
theorem unregistration_execution_race {s : State} (h : Invariant s) {call k : Nat}
    {tool : ToolObject} (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) {d : ToolDef}
    (hd : d ∈ s.tools) (hid : d.id = tool.id) {g : Nat} (hg : d.signal = some g) (x : Input)
    (t : ModelContextTool) (doc : Nat) :
    ∀ p ∈ concurrent s [.execute call k x .none, .abort g, .register t none []] doc,
      ∃ o, (o = .err .notFound ∨ o = .err .notAllowed ∨ o = .err .typeError) ∧
        p.2 = .all [o, .ok, (registerTool (unregisterBySignal s g).1 t none [] doc).2] := by
  have hfresh : g ∉ s.aborted := h.signals_live d hd g hg
  -- After the abort, no tool has the `Tool`'s id, and the new one gets a fresh id.
  have hgone : ∀ d' ∈ (unregisterBySignal s g).1.tools, d'.id ≠ tool.id := by
    rw [unregisterBySignal_of_fresh hfresh]
    intro d' hd' heq
    have := h.id_determines d' (mem_filter_signal.mp hd').1 d hd (heq.trans hid.symm)
    subst this
    exact (mem_filter_signal.mp hd').2 hg
  have hlt : tool.id < s.nextId := by rw [← hid]; exact h.ids_issued d hd
  have hgone' : ∀ d' ∈ (registerTool (unregisterBySignal s g).1 t none [] doc).1.tools,
      d'.id ≠ tool.id := by
    intro d' hd' heq
    rcases (registerTool_evolves _ t none [] doc).tools d' hd' with hd' | hle
    · exact hgone d' hd' heq
    · rw [unregisterBySignal_nextId] at hle
      exact absurd (heq ▸ hle) (Nat.not_le.mpr hlt)
  intro p hp
  have hreg : ∀ s' : State, registerTool s' t none [] doc =
      match registerToolChecks s' t none [] doc with
      | some e => (s', .err e) | none => (addTool s' t none [] doc, .ok) := fun _ => rfl
  simp only [concurrent, syncPhase, syncAction, ht] at hp
  by_cases ha : docAllowed s doc = true
  · cases hx : x.serialize with
    | none =>
      simp only [ha, hx] at hp
      refine ⟨.err .typeError, .inr (.inr rfl), ?_⟩
      cases hc : registerToolChecks (unregisterBySignal s g).1 t none [] doc <;>
        simp [hc, orders, choices, callChoices, asyncPhase, Pending.since, range_three] at hp <;>
        (subst hp; simp [hreg, hc])
    | some json =>
      refine ⟨.err .notFound, .inl rfl, ?_⟩
      cases hc : registerToolChecks (unregisterBySignal s g).1 t none [] doc with
      | some e =>
        have hl : lookup (unregisterBySignal s g).1 tool.source tool.id = none := lookup_none hgone
        simp [ha, hx, hc, orders, insertEverywhere, choices, callChoices, asyncPhase, asyncStep, Pending.since,
          range_three, hl] at hp
        subst hp; simp [hreg, hc]
      | none =>
        have hl : lookup (addTool (unregisterBySignal s g).1 t none [] doc) tool.source tool.id =
            none := by
          refine lookup_none fun d' hd' => ?_
          have := hgone' d'
          rw [registerTool_of_checks hc] at this
          exact this hd'
        simp [ha, hx, hc, orders, insertEverywhere, choices, callChoices, asyncPhase, asyncStep, Pending.since,
          range_three, hl] at hp
        subst hp; simp [hreg, hc]
  · simp only [ha] at hp
    refine ⟨.err .notAllowed, .inr (.inl rfl), ?_⟩
    cases hc : registerToolChecks (unregisterBySignal s g).1 t none [] doc <;>
      simp [hc, orders, choices, callChoices, asyncPhase, Pending.since, range_three] at hp <;>
      (subst hp; simp [hreg, hc])

/-- **Aborting an execution** (the `executeTool()` `signal` and the note on the race between
    cancellation and the tool's own result). Start `executeTool()` with a signal and abort it in
    the same script: in every allowed order the call rejects with `AbortError`, whether or not
    the tool runs, once the call got as far as its signal. -/
theorem cancel_rejects {s : State} {call k : Nat} {tool : ToolObject}
    (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) {x : Input} {json : String}
    (hx : x.serialize = some json) {doc : Nat} (ha : docAllowed s doc = true) :
    ∀ p ∈ concurrent s [.execute call k x .live, .cancel 0] doc,
      p.2 = .all [.err .abort, .ok] := by
  intro p hp
  simp only [concurrent, syncPhase, syncAction, ht, ha, hx] at hp
  simp [orders, insertEverywhere, choices, callChoices, asyncPhase, asyncStep, Pending.since, range_two] at hp
  obtain ⟨-, rfl⟩ := hp
  rfl

/-- **A tool that unregisters itself still completes** (the note in "unregister a tool"):
    "Unregistering a tool does not cancel an execution that has already reached the invoke the
    execute callback steps, even when the ToolExecuteCallback itself performs the
    unregistration." Executing an `unregisterSelf` tool resolves with its result, and afterwards
    the tool, and every other tool registered with its signal, is gone. -/
theorem unregisterSelf_completes {s : State} (h : Invariant s) {call k : Nat}
    {tool : ToolObject} (ht : (s.toolObjects[call]?).bind (·[k]?) = some tool) {d : ToolDef}
    (hl : lookup s tool.source tool.id = some d) (hb : d.behavior = .unregisterSelf)
    {g : Nat} (hg : d.signal = some g) {x : Input} {json : String}
    (hx : x.serialize = some json) (hobj : x.parsesToObject = true) {doc : Nat}
    (ha : docAllowed s doc = true)
    (hexp : toolIsExposed (docOrigin s tool.source) d.exposedOrigins (docOrigin s doc) = true) :
    (executeTool s call k x doc).2 = .result json ∧
    (executeTool s call k x doc).1.tools = s.tools.filter (·.signal != some g) := by
  have hfresh : g ∉ s.aborted := h.signals_live d (mem_lookup hl).1 g hg
  simp [executeTool, ht, ha, hx, hl, hexp, toolExecuteSteps, toolExecuteEffect, callbackEffect,
    callbackAborts, hb, hobj, hg, invokeExecuteCallback, callbackResult, completionOutcome,
    unregisterBySignal_of_fresh hfresh]

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
/-- info: 'WebMCP.unregistration_execution_race' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.unregistration_execution_race
/-- info: 'WebMCP.cancel_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.cancel_rejects
/-- info: 'WebMCP.unregisterSelf_completes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.unregisterSelf_completes
/-- info: 'WebMCP.step_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.step_deterministic
/-- info: 'WebMCP.concurrent_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.concurrent_spec
/-- info: 'WebMCP.executeTool_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.executeTool_cases
/-- info: 'WebMCP.registerToolChecks_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.registerToolChecks_eq_none
/-- info: 'WebMCP.concurrent_not_exposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.concurrent_not_exposed
/-- info: 'WebMCP.asyncStep_not_exposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.asyncStep_not_exposed
