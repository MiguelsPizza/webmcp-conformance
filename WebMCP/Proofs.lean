import WebMCP.Model

/-!
# Properties of the model

Each theorem holds for every state reachable from the empty model context and every sequence of
calls. Several of them discharge an `Assert` step of the spec: they show the assertion can never
fail, which is exactly what the spec's notes argue in prose.
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
  handles_issued : ∀ hs ∈ s.handles, ∀ h ∈ hs, h.id < s.nextId
  /-- A `Tool` object's name is the name of the registration its tool id identifies. -/
  handles_named : ∀ hs ∈ s.handles, ∀ h ∈ hs, ∀ d ∈ s.tools, d.id = h.id → d.name = h.name
  /-- Every registered tool has a valid name. -/
  names_valid : ∀ d ∈ s.tools, validName d.name = true
  /-- Every registered tool has a non-empty description. -/
  descriptions : ∀ d ∈ s.tools, d.description ≠ ""
  /-- No registered tool's registration signal has fired. -/
  signals_live : ∀ d ∈ s.tools, ∀ sig, d.signal = some sig → sig ∉ s.aborted

theorem invariant_init : Invariant {} := by
  constructor <;> simp

/-- What `registerCheck` returning `none` tells us about the arguments. -/
theorem registerCheck_none {s : State} {t : ToolArgs} {sig : Option Nat}
    (h : registerCheck s t sig = none) :
    hasName s t.name = false ∧ validName t.name = true ∧ (newTool s t sig).description ≠ "" ∧
    ∀ g, sig = some g → g ∉ s.aborted := by
  unfold registerCheck at h
  repeat' (split at h; · simp at h)
  rename_i hconv hdup hname hdesc _ _ hsig
  refine ⟨by simpa using hdup, by simpa using hname, ?_, ?_⟩
  · simp only [newTool]
    have hc : converts t = true := by revert hconv; cases converts t <;> simp
    have hsome : t.description.isSome = true := by
      simp only [converts, Bool.and_eq_true] at hc; exact hc.1.1
    obtain ⟨dsc, hdsc⟩ := Option.isSome_iff_exists.mp hsome
    rw [hdsc] at hdesc ⊢
    simpa using hdesc
  · intro g hg hmem
    subst hg
    simp [hmem] at hsig

theorem insert_invariant {s : State} (h : Invariant s) {t : ToolArgs} {sig : Option Nat}
    (hc : registerCheck s t sig = none) : Invariant (insert s t sig) := by
  obtain ⟨hdup, hname, hdesc, hsig⟩ := registerCheck_none hc
  have hfresh : ∀ d ∈ s.tools, d.name ≠ t.name := by
    intro d hd heq
    have := List.any_eq_false.mp hdup d hd
    simp [heq] at this
  constructor
  · simp only [insert, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨h.names_unique, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    subst hb
    exact hfresh d hd
  · simp only [insert, List.mem_append, List.mem_singleton]
    intro d hd d' hd' heq
    rcases hd with hd | rfl <;> rcases hd' with hd' | rfl
    · exact h.id_determines d hd d' hd' heq
    · exact absurd heq (Nat.ne_of_lt (h.ids_issued d hd))
    · exact absurd heq.symm (Nat.ne_of_lt (h.ids_issued d' hd'))
    · rfl
  · simp only [insert, List.mem_append, List.mem_singleton]
    intro d hd
    rcases hd with hd | rfl
    · exact Nat.lt_succ_of_lt (h.ids_issued d hd)
    · exact Nat.lt_succ_self _
  · intro hs hhs hh hmem
    exact Nat.lt_succ_of_lt (h.handles_issued hs hhs hh hmem)
  · simp only [insert, List.mem_append, List.mem_singleton]
    intro hs hhs hh hmem d hd heq
    rcases hd with hd | rfl
    · exact h.handles_named hs hhs hh hmem d hd heq
    · exact absurd heq.symm (Nat.ne_of_lt (h.handles_issued hs hhs hh hmem))
  · simp only [insert, List.mem_append, List.mem_singleton]
    intro d hd
    rcases hd with hd | rfl
    · exact h.names_valid d hd
    · exact hname
  · simp only [insert, List.mem_append, List.mem_singleton]
    intro d hd
    rcases hd with hd | rfl
    · exact h.descriptions d hd
    · exact hdesc
  · simp only [insert, List.mem_append, List.mem_singleton]
    intro d hd g hg
    rcases hd with hd | rfl
    · exact h.signals_live d hd g hg
    · exact hsig g hg

theorem register_invariant {s : State} (h : Invariant s) (t : ToolArgs) (sig : Option Nat) :
    Invariant (register s t sig).1 := by
  unfold register
  split
  · exact h
  · rename_i hc
    exact insert_invariant h hc

theorem abort_invariant {s : State} (h : Invariant s) (sig : Nat) :
    Invariant (abort s sig).1 := by
  unfold abort
  split
  · exact h
  rename_i hnot
  have mem : ∀ {d}, d ∈ s.tools.filter (·.signal != some sig) → d ∈ s.tools :=
    fun hd => (List.mem_filter.mp hd).1
  constructor
  · exact h.names_unique.sublist ((List.filter_sublist).map _)
  · intro d hd d' hd' heq; exact h.id_determines d (mem hd) d' (mem hd') heq
  · intro d hd; exact h.ids_issued d (mem hd)
  · exact h.handles_issued
  · intro hs hhs hh hmem d hd heq; exact h.handles_named hs hhs hh hmem d (mem hd) heq
  · intro d hd; exact h.names_valid d (mem hd)
  · intro d hd; exact h.descriptions d (mem hd)
  · intro d hd g hg hga
    have hf := (List.mem_filter.mp hd).2
    simp only [List.mem_cons] at hga
    rcases hga with rfl | hga
    · simp [hg] at hf
    · exact h.signals_live d (mem hd) g hg hga

theorem getTools_invariant {s : State} (h : Invariant s) : Invariant (getTools s).1 := by
  have hmem : ∀ {d}, d ∈ sortTools s.tools ↔ d ∈ s.tools :=
    fun {_} => (List.mergeSort_perm _ _).mem_iff
  constructor
  · exact h.names_unique
  · exact h.id_determines
  · exact h.ids_issued
  · simp only [getTools, List.mem_append, List.mem_singleton]
    intro hs hhs hh hmem'
    rcases hhs with hhs | rfl
    · exact h.handles_issued hs hhs hh hmem'
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem'
      exact h.ids_issued d (hmem.mp hd)
  · simp only [getTools, List.mem_append, List.mem_singleton]
    intro hs hhs hh hmem' d hd heq
    rcases hhs with hhs | rfl
    · exact h.handles_named hs hhs hh hmem' d hd heq
    · obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hmem'
      have := h.id_determines d hd d0 (hmem.mp hd0) heq
      subst this
      rfl
  · exact h.names_valid
  · exact h.descriptions
  · exact h.signals_live

theorem execute_state (s : State) (c i : Nat) (x : Input) : (execute s c i x).1 = s := by
  unfold execute
  repeat' split
  all_goals rfl

theorem registerAbortSync_invariant {s : State} (h : Invariant s) (t : ToolArgs) (sig : Nat) :
    Invariant (registerAbortSync s t sig).1 :=
  abort_invariant (register_invariant h t (some sig)) sig

theorem step_invariant {s : State} (h : Invariant s) (op : Op) : Invariant (step s op).1 := by
  cases op with
  | register t sig => exact register_invariant h t sig
  | registerAbortSync t sig => exact registerAbortSync_invariant h t sig
  | abort sig => exact abort_invariant h sig
  | getTools => exact getTools_invariant h
  | execute c i x => simp only [step, execute_state]; exact h

/-- The invariant holds after any sequence of calls. -/
theorem run_invariant {s : State} (h : Invariant s) (ops : List Op) :
    Invariant (run s ops).1 := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih (step_invariant h op)

/-- The invariant holds in every reachable state. -/
theorem reachable_invariant (ops : List Op) : Invariant (run {} ops).1 :=
  run_invariant invariant_init ops

/-- `getTools()` never returns two tools with the same name. -/
theorem getTools_names_unique {s : State} (h : Invariant s) :
    ∃ ts, (getTools s).2 = .tools ts ∧ (ts.map (·.name)).Nodup := by
  refine ⟨_, rfl, ?_⟩
  have hp := ((List.mergeSort_perm s.tools (fun a b => decide (a.name ≤ b.name))).map
    (·.name)).nodup_iff
  simpa [List.map_map, ToolDef.view, sortTools, Function.comp_def] using hp.mpr h.names_unique

/-- A call that fails leaves the model context unchanged (`registerTool()` rejects before it
    adds anything). -/
theorem register_failure_no_effect (s : State) (t : ToolArgs) (sig : Option Nat) (e : Err)
    (h : (register s t sig).2 = .err e) : (register s t sig).1 = s := by
  unfold register at h ⊢
  split at h
  · rfl
  · simp at h

/-! ### The `executeTool()` asserts

  After looking up `targetToolMap[toolId]`, `executeTool()` asserts that the definition's name is
  the `Tool`'s name. -/

/-- The spec's `Assert: tool definition's name is tool's name`: when a `Tool` object's tool id
    is still in the tool map, the definition found there has that `Tool`'s name, so the call runs
    exactly the registration `getTools()` returned. -/
theorem execute_assert_name {s : State} (h : Invariant s) {c k : Nat} {hd : Handle}
    (hh : (s.handles[c]?).bind (·[k]?) = some hd) {d : ToolDef}
    (hf : s.tools.find? (·.id == hd.id) = some d) : d.name = hd.name := by
  obtain ⟨hs, hhs, hk⟩ : ∃ hs, s.handles[c]? = some hs ∧ hs[k]? = some hd := by
    cases hc : s.handles[c]? with
    | none => simp [hc] at hh
    | some hs => exact ⟨hs, rfl, by simpa [hc] using hh⟩
  have hdm := List.mem_of_find?_eq_some hf
  have hid : d.id = hd.id := by simpa using List.find?_some hf
  exact h.handles_named hs (List.mem_of_getElem? hhs) hd (List.mem_of_getElem? hk) d hdm hid

/-! ### Tool ids are never reused

  This is the property the `Tool` interface (spec PR #348) was introduced for: a `Tool` names
  one registration, so once that registration is gone, the `Tool` can never run anything again,
  even if a new tool takes the same name. -/

theorem register_nextId_ge (s : State) (t : ToolArgs) (sig : Option Nat) :
    s.nextId ≤ (register s t sig).1.nextId := by
  unfold register
  split
  · exact Nat.le_refl _
  · exact Nat.le_succ _

theorem register_retired {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (t : ToolArgs) (sig : Option Nat) : n ∉ ids (register s t sig).1 := by
  unfold register
  split
  · exact hn
  · simp only [ids, insert, newTool, List.map_append, List.mem_append, List.map_cons,
      List.map_nil, List.mem_singleton, not_or]
    exact ⟨hn, Nat.ne_of_lt hlt⟩

theorem abort_retired {s : State} (n : Nat) (hn : n ∉ ids s) (sig : Nat) :
    n ∉ ids (abort s sig).1 := by
  unfold abort
  split
  · exact hn
  · intro hm
    apply hn
    simp only [ids, List.mem_map] at hm ⊢
    obtain ⟨d, hd, rfl⟩ := hm
    exact ⟨d, (List.mem_filter.mp hd).1, rfl⟩

theorem abort_nextId (s : State) (sig : Nat) : (abort s sig).1.nextId = s.nextId := by
  unfold abort; split <;> rfl

theorem retired_stays_retired {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (op : Op) : n < (step s op).1.nextId ∧ n ∉ ids (step s op).1 := by
  cases op with
  | register t sig =>
    exact ⟨Nat.lt_of_lt_of_le hlt (register_nextId_ge s t sig), register_retired n hlt hn t sig⟩
  | registerAbortSync t sig =>
    simp only [step, registerAbortSync]
    refine ⟨?_, abort_retired n (register_retired n hlt hn t (some sig)) sig⟩
    rw [abort_nextId]
    exact Nat.lt_of_lt_of_le hlt (register_nextId_ge s t (some sig))
  | abort sig =>
    simp only [step]
    exact ⟨by rw [abort_nextId]; exact hlt, abort_retired n hn sig⟩
  | getTools => exact ⟨hlt, hn⟩
  | execute c i x => simp only [step, execute_state]; exact ⟨hlt, hn⟩

theorem retired_stays_retired_run {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) : n ∉ ids (run s ops).1 := by
  induction ops generalizing s with
  | nil => exact hn
  | cons op ops ih =>
    have := retired_stays_retired n hlt hn op
    exact ih this.1 this.2

/-- Executing a `Tool` whose registration is gone fails with `NotFoundError` (or `TypeError`,
    if the input itself cannot be serialized), whatever the page has done since. -/
theorem stale_handle_not_found {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) (c k : Nat) (x : Input) (name : String)
    (hh : ((run s ops).1.handles[c]?).bind (·[k]?) = some ⟨n, name⟩) :
    (execute (run s ops).1 c k x).2 = .err .notFound ∨
    (execute (run s ops).1 c k x).2 = .err .typeError := by
  have hgone := retired_stays_retired_run n hlt hn ops
  generalize (run s ops).1 = s' at hh hgone ⊢
  unfold execute
  rw [hh]
  simp only
  cases x.serialize with
  | none => exact Or.inr rfl
  | some json =>
    have : s'.tools.find? (·.id == n) = none := by
      rw [List.find?_eq_none]
      intro d hd heq
      apply hgone
      simp only [beq_iff_eq] at heq
      exact List.mem_map.mpr ⟨d, hd, heq⟩
    simp [this]

end WebMCP

-- Fail the build if any theorem above comes to rest on `sorry` or an extra axiom.
/-- info: 'WebMCP.reachable_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.reachable_invariant
/-- info: 'WebMCP.getTools_names_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.getTools_names_unique
/-- info: 'WebMCP.execute_assert_name' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.execute_assert_name
/-- info: 'WebMCP.stale_handle_not_found' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.stale_handle_not_found
/-- info: 'WebMCP.register_failure_no_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WebMCP.register_failure_no_effect
