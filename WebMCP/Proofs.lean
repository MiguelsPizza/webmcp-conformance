import WebMCP.Model

/-! Properties proved about the model, for every state and every sequence of operations. -/
namespace WebMCP

/-- What the spec promises about a model context's tool map at all times. -/
structure Inv (s : State) : Prop where
  names_unique : (s.tools.map (·.name)).Nodup
  ids_unique   : (ids s).Nodup
  ids_issued   : ∀ d ∈ s.tools, d.id < s.nextId
  names_valid  : ∀ d ∈ s.tools, validName d.name = true
  descriptions : ∀ d ∈ s.tools, d.description ≠ ""

theorem inv_init : Inv {} := by
  constructor <;> simp [ids]

theorem register_inv {s : State} (h : Inv s) (t : ToolArgs) (sig : Option Nat) :
    Inv (register s t sig).1 := by
  unfold register
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  split
  · exact h
  rename_i hdup hname hdesc _ _ _
  simp only [Bool.not_eq_true] at hdup
  simp only [Bool.not_eq_true] at hname
  simp only [beq_iff_eq] at hdesc
  have hdup' : ∀ d ∈ s.tools, d.name ≠ t.name := by
    intro d hd heq
    have := List.any_eq_false.mp hdup d hd
    simp [heq] at this
  constructor
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨h.names_unique, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    subst hb
    exact hdup' d hd
  · simp only [ids, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨h.ids_unique, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    subst hb
    exact Nat.ne_of_lt (h.ids_issued d hd)
  · intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact Nat.lt_succ_of_lt (h.ids_issued d hd)
    · exact Nat.lt_succ_self _
  · intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact h.names_valid d hd
    · simpa using hname
  · intro d hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact h.descriptions d hd
    · exact hdesc

theorem abort_inv {s : State} (h : Inv s) (sig : Nat) : Inv (abort s sig).1 := by
  unfold abort
  split
  · exact h
  constructor
  · exact h.names_unique.sublist ((List.filter_sublist).map _)
  · exact h.ids_unique.sublist ((List.filter_sublist).map _)
  · intro d hd; exact h.ids_issued d ((List.mem_filter.mp hd).1)
  · intro d hd; exact h.names_valid d ((List.mem_filter.mp hd).1)
  · intro d hd; exact h.descriptions d ((List.mem_filter.mp hd).1)

theorem getTools_tools (s : State) : (getTools s).1.tools = s.tools := rfl
theorem getTools_nextId (s : State) : (getTools s).1.nextId = s.nextId := rfl

theorem execute_state (s : State) (c i : Nat) (x : Input) : (execute s c i x).1 = s := by
  unfold execute
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

theorem step_inv {s : State} (h : Inv s) (op : Op) : Inv (step s op).1 := by
  cases op with
  | register t sig => exact register_inv h t sig
  | abort sig => exact abort_inv h sig
  | getTools => exact ⟨h.names_unique, h.ids_unique, h.ids_issued, h.names_valid, h.descriptions⟩
  | execute c i x => simp only [step, execute_state]; exact h

/-- The invariant holds after any sequence of API calls. -/
theorem run_inv {s : State} (h : Inv s) (ops : List Op) : Inv (run s ops).1 := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih (step_inv h op)

/-- getTools() never returns two tools with the same name. -/
theorem getTools_names_unique {s : State} (h : Inv s) :
    ∃ names, (getTools s).2 = .tools names ∧ names.Nodup := by
  refine ⟨_, rfl, ?_⟩
  have hp : (sortTools (s.tools.map fun d => (d.id, d.name))).Perm
      (s.tools.map fun d => (d.id, d.name)) := List.mergeSort_perm _ _
  have := (hp.map (·.2)).nodup_iff.mpr (by simpa [List.map_map] using h.names_unique)
  exact this

/-! ### Tool ids are never reused

  This is the property the `Tool` interface (spec PR #348) was introduced for: a `Tool`
  handle names one registration, so once that registration is gone, the handle can never
  run anything again, even if a new tool takes the same name. -/

theorem register_nextId_ge (s : State) (t : ToolArgs) (sig : Option Nat) :
    s.nextId ≤ (register s t sig).1.nextId := by
  unfold register
  repeat' split
  all_goals simp

theorem retired_stays_retired {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (op : Op) : n < (step s op).1.nextId ∧ n ∉ ids (step s op).1 := by
  cases op with
  | register t sig =>
    refine ⟨Nat.lt_of_lt_of_le hlt (register_nextId_ge s t sig), ?_⟩
    simp only [step]
    unfold register
    repeat' split
    all_goals first
      | exact hn
      | (simp only [ids, List.map_append, List.mem_append, List.map_cons, List.map_nil,
                    List.mem_singleton, not_or]
         exact ⟨hn, Nat.ne_of_lt hlt⟩)
  | abort sig =>
    simp only [step]
    unfold abort
    split
    · exact ⟨hlt, hn⟩
    · refine ⟨hlt, fun hm => hn ?_⟩
      simp only [ids, List.mem_map] at hm ⊢
      obtain ⟨d, hd, rfl⟩ := hm
      exact ⟨d, (List.mem_filter.mp hd).1, rfl⟩
  | getTools => exact ⟨hlt, hn⟩
  | execute c i x => simp only [step, execute_state]; exact ⟨hlt, hn⟩

theorem retired_stays_retired_run {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) : n ∉ ids (run s ops).1 := by
  induction ops generalizing s with
  | nil => exact hn
  | cons op ops ih =>
    have := retired_stays_retired n hlt hn op
    exact ih this.1 this.2

/-- Executing a handle whose registration is gone fails with NotFoundError (or TypeError, if
    the input itself cannot be serialized), whatever the page has done since. -/
theorem stale_handle_not_found {s : State} (n : Nat) (hlt : n < s.nextId) (hn : n ∉ ids s)
    (ops : List Op) (c k : Nat) (x : Input) (name : String)
    (hh : ((run s ops).1.handles[c]?).bind (·[k]?) = some (n, name)) :
    (execute (run s ops).1 c k x).2 = .err .notFound ∨
    (execute (run s ops).1 c k x).2 = .err .typeError := by
  have hgone := retired_stays_retired_run n hlt hn ops
  generalize (run s ops).1 = s' at hh hgone ⊢
  unfold execute
  cases x with
  | unserializable => exact Or.inr rfl
  | obj m =>
    simp only
    rw [hh]
    have : s'.tools.find? (·.id == n) = none := by
      rw [List.find?_eq_none]
      intro d hd heq
      apply hgone
      simp only [beq_iff_eq] at heq
      exact List.mem_map.mpr ⟨d, hd, heq⟩
    simp [this]

end WebMCP

-- Check that nothing above rests on `sorry` or extra axioms.
#print axioms WebMCP.run_inv
#print axioms WebMCP.getTools_names_unique
#print axioms WebMCP.stale_handle_not_found
