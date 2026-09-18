import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.TMachine
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

/-!
# From structured machines to Minsky machines

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, via the
undecidability of the halting problem for Minsky machines (Minsky 1967;
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 3).

A structured machine `T : TMachine K σ` over a finite state type, together with
a numbering `e : σ ≃ Fin (N + 1)` sending the stop state to `0`, gives a
Minsky machine `T.toMachine e he0` with single-glass commands.  An `add`
instruction becomes an `Add` command, and a `test` instruction becomes the pair
of commands `Sub` (glass nonempty) and zero test (glass empty).  The result is
deterministic, and it reaches the stop configuration from `⟨e s, g⟩` exactly
when `T` reaches its stop configuration from `(s, g)`
(`TMachine.exists_minsky_of_tmachine`).
-/

namespace GroupApproximation.Full.Kharlampovich.MinskySim

variable {K : ℕ} {σ : Type}

/-- The Minsky commands attached to a state with a given instruction
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def entries {N : ℕ} (e : σ → Fin (N + 1)) (a : σ) :
    Option (TInstr K σ) → List (Fin (N + 1) × Minsky.Instr K N)
  | none => []
  | some (TInstr.add n j) => [(e a, Minsky.Instr.add n (e j))]
  | some (TInstr.test n jp jz) =>
      [(e a, Minsky.Instr.sub n (e jp)), (e a, Minsky.Instr.zero n (e jz))]

/-- Commands attached to `a` start at `e a`, and exist only when `a` has an
instruction (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem fst_of_mem_entries {N : ℕ} (e : σ → Fin (N + 1)) (a : σ) {o : Option (TInstr K σ)}
    {r : Fin (N + 1) × Minsky.Instr K N} (hr : r ∈ entries e a o) :
    r.1 = e a ∧ o ≠ none := by
  cases o with
  | none =>
    have hr' : r ∈ ([] : List (Fin (N + 1) × Minsky.Instr K N)) := hr
    exact absurd hr' List.not_mem_nil
  | some i =>
    cases i with
    | add n j =>
      have hr' : r = (e a, Minsky.Instr.add n (e j)) := List.mem_singleton.mp hr
      subst hr'
      exact ⟨rfl, Option.some_ne_none _⟩
    | test n jp jz =>
      rcases List.mem_cons.mp hr with hr' | hr'
      · subst hr'
        exact ⟨rfl, Option.some_ne_none _⟩
      · have hr'' : r = (e a, Minsky.Instr.zero n (e jz)) := List.mem_singleton.mp hr'
        subst hr''
        exact ⟨rfl, Option.some_ne_none _⟩

/-- Embedding structured configurations as Minsky configurations
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def emb {N : ℕ} (e : σ → Fin (N + 1)) (c : σ × (Fin K → ℕ)) : Minsky.Cfg K N :=
  ⟨e c.1, c.2⟩

/-- Extensionality for Minsky configurations
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem cfg_ext {N : ℕ} :
    ∀ {x y : Minsky.Cfg K N}, x.state = y.state → x.glass = y.glass → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

/-- A numbering of a nonempty finite type sending a given element to `0`
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem exists_equiv [Fintype σ] (s₀ : σ) :
    ∃ (N : ℕ) (e : σ ≃ Fin (N + 1)), e s₀ = 0 := by
  have hpos : 0 < Fintype.card σ := (Fintype.equivFin σ s₀).pos
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card σ = n + 1 := ⟨Fintype.card σ - 1, by omega⟩
  refine ⟨n, (Fintype.equivFinOfCardEq hn).trans
    (Equiv.swap (Fintype.equivFinOfCardEq hn s₀) 0), ?_⟩
  rw [Equiv.trans_apply, Equiv.swap_apply_left]

namespace TMachine

variable (T : TMachine K σ)

/-- The Minsky machine of a structured machine
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def toMachine {N : ℕ} (e : σ ≃ Fin (N + 1)) (he0 : e T.stop = 0) : Minsky.Machine K N where
  prog := (List.finRange (N + 1)).flatMap fun i ↦ entries e (e.symm i) (T.δ (e.symm i))
  stop_terminal := by
    intro r hr
    obtain ⟨i, _, hri⟩ := List.mem_flatMap.mp hr
    obtain ⟨h1, h2⟩ := fst_of_mem_entries e (e.symm i) hri
    rw [h1, Equiv.apply_symm_apply]
    intro h0
    apply h2
    have hs : e.symm i = T.stop := by rw [h0, ← he0, Equiv.symm_apply_apply]
    rw [hs, T.δ_stop]

variable {N : ℕ} (e : σ ≃ Fin (N + 1)) (he0 : e T.stop = 0)

/-- The commands of each state belong to the program
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem mem_prog (a : σ) {r : Fin (N + 1) × Minsky.Instr K N}
    (hr : r ∈ entries e a (T.δ a)) : r ∈ (T.toMachine e he0).prog := by
  have hr' : r ∈ entries e (e.symm (e a)) (T.δ (e.symm (e a))) := by
    rw [Equiv.symm_apply_apply]
    exact hr
  show r ∈ (List.finRange (N + 1)).flatMap fun i ↦ entries e (e.symm i) (T.δ (e.symm i))
  exact List.mem_flatMap.mpr ⟨e a, List.mem_finRange _, hr'⟩

/-- A structured step is a Minsky step
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem step_emb {c d : σ × (Fin K → ℕ)} (h : T.step c = some d) :
    (T.toMachine e he0).Step (emb e c) (emb e d) := by
  obtain ⟨a, g⟩ := c
  cases hδ : T.δ a with
  | none =>
    rw [T.step_eq_none_of_δ hδ g] at h
    cases h
  | some i =>
    rw [T.step_of_δ hδ g] at h
    have hd : i.exec g = d := Option.some_inj.mp h
    subst hd
    show ∃ r ∈ (T.toMachine e he0).prog,
      r.1 = (emb e (a, g)).state ∧ r.2.Fires (emb e (a, g)) (emb e (i.exec g))
    cases i with
    | add n j =>
      refine Exists.intro (e a, Minsky.Instr.add n (e j)) (And.intro ?_ (And.intro rfl ?_))
      · apply T.mem_prog e he0 a
        rw [hδ]
        exact List.mem_singleton.mpr rfl
      · exact And.intro rfl rfl
    | test n jp jz =>
      by_cases hg : g n = 0
      · refine Exists.intro (e a, Minsky.Instr.zero n (e jz)) (And.intro ?_ (And.intro rfl ?_))
        · apply T.mem_prog e he0 a
          rw [hδ]
          exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
        · rw [TInstr.exec_test_zero n jp jz hg]
          exact And.intro hg (And.intro rfl rfl)
      · refine Exists.intro (e a, Minsky.Instr.sub n (e jp)) (And.intro ?_ (And.intro rfl ?_))
        · apply T.mem_prog e he0 a
          rw [hδ]
          exact List.mem_cons_self
        · rw [TInstr.exec_test, if_neg hg]
          have hpos : 0 < g n := by omega
          exact And.intro hpos (And.intro rfl rfl)

/-- A Minsky step from an embedded configuration is an embedded structured step
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem exists_step_of_step_emb {c : σ × (Fin K → ℕ)} {x : Minsky.Cfg K N}
    (h : (T.toMachine e he0).Step (emb e c) x) : ∃ d, T.step c = some d ∧ x = emb e d := by
  obtain ⟨a, g⟩ := c
  obtain ⟨r, hr, hrs, hfire⟩ := h
  have hr2 :
      r ∈ (List.finRange (N + 1)).flatMap fun i ↦ entries e (e.symm i) (T.δ (e.symm i)) := hr
  obtain ⟨idx, _, hri⟩ := List.mem_flatMap.mp hr2
  obtain ⟨hr1, _⟩ := fst_of_mem_entries e (e.symm idx) hri
  have hia : e.symm idx = a := by
    apply e.injective
    rw [← hr1]
    exact hrs
  have hri' : r ∈ entries e a (T.δ a) := by
    rw [← hia]
    exact hri
  cases hδ : T.δ a with
  | none =>
    rw [hδ] at hri'
    have hr' : r ∈ ([] : List (Fin (N + 1) × Minsky.Instr K N)) := hri'
    exact absurd hr' List.not_mem_nil
  | some ins =>
    rw [hδ] at hri'
    refine ⟨ins.exec g, T.step_of_δ hδ g, ?_⟩
    cases ins with
    | add n j =>
      have hr' : r = (e a, Minsky.Instr.add n (e j)) := List.mem_singleton.mp hri'
      subst hr'
      obtain ⟨hs, hgl⟩ := hfire
      exact cfg_ext hs hgl
    | test n jp jz =>
      rcases List.mem_cons.mp hri' with hr' | hr'
      · subst hr'
        obtain ⟨hpos, hs, hgl⟩ := hfire
        have hpos' : 0 < g n := hpos
        have hne : g n ≠ 0 := by omega
        rw [TInstr.exec_test, if_neg hne]
        exact cfg_ext hs hgl
      · have hr'' : r = (e a, Minsky.Instr.zero n (e jz)) := List.mem_singleton.mp hr'
        subst hr''
        obtain ⟨hz, hs, hgl⟩ := hfire
        have hz' : g n = 0 := hz
        rw [TInstr.exec_test_zero n jp jz hz']
        exact cfg_ext hs hgl

/-- The Minsky machine of a structured machine is deterministic
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem toMachine_deterministic : (T.toMachine e he0).Deterministic := by
  intro x y₁ y₂ h₁ h₂
  have hx : x = emb e (e.symm x.state, x.glass) :=
    cfg_ext (Equiv.apply_symm_apply e x.state).symm rfl
  rw [hx] at h₁ h₂
  obtain ⟨d₁, hd₁, rfl⟩ := T.exists_step_of_step_emb e he0 h₁
  obtain ⟨d₂, hd₂, rfl⟩ := T.exists_step_of_step_emb e he0 h₂
  exact congrArg (emb e) (Option.some_inj.mp (hd₁.symm.trans hd₂))

/-- Structured runs are Minsky runs
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem reaches_emb {c d : σ × (Fin K → ℕ)} (h : Relation.ReflTransGen T.StepRel c d) :
    (T.toMachine e he0).Reaches (emb e c) (emb e d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (T.step_emb e he0 hbc)

/-- Minsky runs from embedded configurations are embedded structured runs
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem exists_of_reaches_emb {c : σ × (Fin K → ℕ)} {x : Minsky.Cfg K N}
    (h : (T.toMachine e he0).Reaches (emb e c) x) :
    ∃ d, Relation.ReflTransGen T.StepRel c d ∧ x = emb e d := by
  have h' : Relation.ReflTransGen (T.toMachine e he0).Step (emb e c) x := h
  clear h
  induction h' with
  | refl => exact ⟨c, Relation.ReflTransGen.refl, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨d, hd, rfl⟩ := ih
    obtain ⟨d', hd', rfl⟩ := T.exists_step_of_step_emb e he0 hbc
    exact ⟨d', Relation.ReflTransGen.tail hd hd', rfl⟩

/-- Halting transfers along the embedding
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem reaches_stopCfg_iff (s : σ) (g : Fin K → ℕ) :
    (T.toMachine e he0).Reaches ⟨e s, g⟩ (Minsky.stopCfg K N) ↔
      Relation.ReflTransGen T.StepRel (s, g) T.stopc := by
  have hstop : emb e T.stopc = Minsky.stopCfg K N := cfg_ext he0 rfl
  constructor
  · intro h
    obtain ⟨d, hd, hdx⟩ := T.exists_of_reaches_emb e he0 (c := (s, g)) h
    have hd1 : e d.1 = e T.stop := by
      rw [he0]
      exact (congrArg Minsky.Cfg.state hdx).symm
    have hd2 : d.2 = fun _ ↦ 0 := (congrArg Minsky.Cfg.glass hdx).symm
    have hdd : d = T.stopc := by
      obtain ⟨d1, d2⟩ := d
      have h1 : d1 = T.stop := e.injective hd1
      have h2 : d2 = fun _ ↦ 0 := hd2
      subst h1
      subst h2
      rfl
    rw [← hdd]
    exact hd
  · intro h
    have h' := T.reaches_emb e he0 h
    rw [hstop] at h'
    exact h'

/-- **Structured machines give deterministic Minsky machines**: halting of a
structured machine from `(s, g)` is halting of a deterministic Minsky machine
from `⟨s', g⟩` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem exists_minsky_of_tmachine [Fintype σ] (s : σ) :
    ∃ (N : ℕ) (M : Minsky.Machine K N) (s' : Fin (N + 1)), M.Deterministic ∧
      ∀ g : Fin K → ℕ,
        (M.Reaches ⟨s', g⟩ (Minsky.stopCfg K N) ↔ ∃ n, T.next^[n] (s, g) = T.stopc) := by
  obtain ⟨N, e, he0⟩ := exists_equiv T.stop
  exact ⟨N, T.toMachine e he0, e s, T.toMachine_deterministic e he0,
    fun g ↦ (T.reaches_stopCfg_iff e he0 s g).trans (T.reaches_stopc_iff (s, g))⟩

end TMachine

end GroupApproximation.Full.Kharlampovich.MinskySim
