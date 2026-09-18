import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Elim
import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.SystemDefs

/-!
# Feasibility of polynomial systems via the prenex decision procedure

`non_mf_group_notes.tex`, `thm:mf-arithmetic`, proof step "Fixed-dimensional
feasibility is decidable over the real closed field".  A system
`p = 0 (p ∈ S.1)`, `0 ≤ q (q ∈ S.2)` has a real solution iff
`decidePrenex (systemPrenex S) = true` (`existsSystem_iff_decidePrenex`).  The
polynomials involve only the variables `x_j` with `j < varBound (S.1 ++ S.2)`.  So a
solution can be truncated to those variables, which are exactly the variables that
`systemPrenex S` quantifies.
-/

namespace GroupApproximation.Full.NN11b

/-! ## Existential prefixes -/

/-- An existential prefix over the variables in `l` is an existential quantifier over
all assignments that agree with `ρ` outside `l`. -/
theorem pHolds_exPrefix (f : List (List Atom)) : ∀ (l : List ℕ) (ρ : ℕ → ℝ),
    PHolds (l.map fun i => (true, i)) f ρ ↔
      ∃ x : ℕ → ℝ, (∀ j, j ∉ l → x j = ρ j) ∧ qfHolds x f
  | [], ρ => by
      show qfHolds ρ f ↔ _
      constructor
      · intro h
        exact ⟨ρ, fun _ _ => rfl, h⟩
      · rintro ⟨x, hx, h⟩
        have e : x = ρ := funext fun j => hx j List.not_mem_nil
        rw [← e]
        exact h
  | i :: l, ρ => by
      show (∃ r : ℝ, PHolds (l.map fun i => (true, i)) f (Function.update ρ i r)) ↔ _
      constructor
      · rintro ⟨r, h⟩
        obtain ⟨x, hx, h'⟩ := (pHolds_exPrefix f l _).1 h
        refine ⟨x, fun j hj => ?_, h'⟩
        rw [hx j fun hj' => hj (List.mem_cons.2 (Or.inr hj'))]
        exact Function.update_of_ne (fun e => hj (List.mem_cons.2 (Or.inl e))) r ρ
      · rintro ⟨x, hx, h⟩
        refine ⟨x i, (pHolds_exPrefix f l _).2 ⟨x, fun j hj => ?_, h⟩⟩
        by_cases e : j = i
        · rw [e, Function.update_self]
        · rw [Function.update_of_ne e]
          exact hx j fun hj' => (List.mem_cons.1 hj').elim e hj

/-! ## The matrix of `systemPrenex` -/

theorem qfHolds_nonnegQF (ρ : ℕ → ℝ) : ∀ qs : List MvP,
    qfHolds ρ (nonnegQF qs) ↔ ∀ q ∈ qs, 0 ≤ mvEval ρ q
  | [] => by
      show qfHolds ρ [[]] ↔ _
      rw [qfHolds_cons]
      exact ⟨fun _ _ hq => absurd hq List.not_mem_nil, fun _ => Or.inl (guardHolds_nil ρ)⟩
  | q :: qs => by
      show qfHolds ρ (qfAnd [[(true, q)], [(false, q)]] (nonnegQF qs)) ↔ _
      rw [qfHolds_and, qfHolds_nonnegQF ρ qs, qfHolds_cons, qfHolds_cons,
        iff_false_intro (qfHolds_nil ρ), or_false, guardHolds_singleton, guardHolds_singleton,
        atomHolds_true, atomHolds_false]
      constructor
      · rintro ⟨h1, h2⟩ p hp
        rcases List.mem_cons.1 hp with e | hp'
        · rw [e]
          rcases h1 with h | h
          · exact le_of_lt h
          · exact le_of_eq h.symm
        · exact h2 p hp'
      · intro h
        exact ⟨(lt_or_eq_of_le (h q (List.mem_cons.2 (Or.inl rfl)))).imp id Eq.symm,
          fun p hp => h p (List.mem_cons.2 (Or.inr hp))⟩

theorem guardHolds_eqs (ρ : ℕ → ℝ) (ps : List MvP) :
    guardHolds ρ (ps.map fun p => (false, p)) ↔ ∀ p ∈ ps, mvEval ρ p = 0 := by
  unfold guardHolds
  constructor
  · intro h p hp
    exact h (false, p) (List.mem_map.2 ⟨p, hp, rfl⟩)
  · intro h a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact h p hp

theorem qfHolds_system (x : ℕ → ℝ) (S : List MvP × List MvP) :
    qfHolds x (qfAnd [S.1.map fun p => (false, p)] (nonnegQF S.2)) ↔
      (∀ p ∈ S.1, mvEval x p = 0) ∧ ∀ p ∈ S.2, 0 ≤ mvEval x p := by
  rw [qfHolds_and, qfHolds_nonnegQF, qfHolds_cons, iff_false_intro (qfHolds_nil x), or_false,
    guardHolds_eqs]

/-! ## Only the variables below `varBound` matter -/

theorem monoEval_congr : ∀ (e : List ℕ) (x y : ℕ → ℝ), (∀ j, j < e.length → x j = y j) →
    monoEval x e = monoEval y e
  | [], _, _, _ => rfl
  | k :: e, x, y, h => by
      rw [monoEval_cons, monoEval_cons, h 0 (Nat.succ_pos _),
        monoEval_congr e (fun j => x (j + 1)) (fun j => y (j + 1))
          fun j hj => h (j + 1) (Nat.succ_lt_succ hj)]

theorem mvEval_congr (x y : ℕ → ℝ) : ∀ p : MvP,
    (∀ m ∈ p, ∀ j, j < m.2.length → x j = y j) → mvEval x p = mvEval y p
  | [], _ => rfl
  | m :: p, h => by
      rw [mvEval_cons, mvEval_cons, monoEval_congr m.2 x y (h m (List.mem_cons.2 (Or.inl rfl))),
        mvEval_congr x y p fun m' hm' => h m' (List.mem_cons.2 (Or.inr hm'))]

theorem le_foldr_max : ∀ (ns : List ℕ) (n : ℕ), n ∈ ns → n ≤ ns.foldr max 0
  | [], _, h => absurd h List.not_mem_nil
  | k :: ns, n, h => by
      rw [List.foldr_cons]
      rcases List.mem_cons.1 h with e | h'
      · rw [e]
        exact Nat.le_max_left _ _
      · exact le_trans (le_foldr_max ns n h') (Nat.le_max_right _ _)

theorem le_varBound (l : List MvP) (p : MvP) (hp : p ∈ l) (m : ℤ × List ℕ) (hm : m ∈ p) :
    m.2.length ≤ varBound l := by
  show m.2.length ≤ (l.flatMap fun p => p.map fun m => m.2.length).foldr max 0
  exact le_foldr_max _ _ (List.mem_flatMap.2 ⟨p, hp, List.mem_map.2 ⟨m, hm, rfl⟩⟩)

/-! ## Feasibility -/

/-- **Feasibility of a polynomial system is decided by `decidePrenex`**: the system
`p = 0 (p ∈ S.1)`, `0 ≤ q (q ∈ S.2)` has a real solution iff
`decidePrenex (systemPrenex S) = true`. -/
theorem existsSystem_iff_decidePrenex (S : List MvP × List MvP) :
    (∃ x : ℕ → ℝ, (∀ p ∈ S.1, mvEval x p = 0) ∧ ∀ p ∈ S.2, 0 ≤ mvEval x p) ↔
      decidePrenex (systemPrenex S) = true := by
  rw [decidePrenex_iff]
  show _ ↔ PHolds ((List.range (varBound (S.1 ++ S.2))).map fun i => (true, i))
    (qfAnd [S.1.map fun p => (false, p)] (nonnegQF S.2)) (fun _ => 0)
  rw [pHolds_exPrefix]
  constructor
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨fun j => if j < varBound (S.1 ++ S.2) then x j else 0, fun j hj => ?_, ?_⟩
    · have hj' : ¬ j < varBound (S.1 ++ S.2) := fun h => hj (List.mem_range.2 h)
      exact if_neg hj'
    · rw [qfHolds_system]
      have e : ∀ p ∈ S.1 ++ S.2,
          mvEval (fun j => if j < varBound (S.1 ++ S.2) then x j else 0) p = mvEval x p :=
        fun p hp => mvEval_congr _ _ p fun m hm _ hj =>
          if_pos (lt_of_lt_of_le hj (le_varBound _ p hp m hm))
      refine ⟨fun p hp => (e p (List.mem_append.2 (Or.inl hp))).trans (hx1 p hp),
        fun p hp => ?_⟩
      rw [e p (List.mem_append.2 (Or.inr hp))]
      exact hx2 p hp
  · rintro ⟨x, _, h⟩
    exact ⟨x, (qfHolds_system x S).1 h⟩

end GroupApproximation.Full.NN11b
