import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepDescentList
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-58: a step relation has at most one descent

Lane gl-p07-58.  Pure list combinatorics for the converse
`WitnessCurveSublistStepStatement → WitnessStepDescentStatement`.  Certifies no printed
sentence.  NOT COMPILED.

* `witnessStepDescent_rotate_of_mem_steps`: when `2 ≤ |l|`, every cyclic step `(x, y)` of `l`
  is a rotation step `l.rotate n = s ++ x :: y :: t`.
* `witnessStepDescent_turnSum_le_of_unique`: a duplicate-free list of steps with at most one
  descent turns at most once.
* `witnessStepDescent_first_of_descent`: a `StepNext` step that is a descent ends at the
  `w`-first entry of `l`.  Two such entries coincide (`witnessStepDescent_eq_of_first`).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

section DescentUnique

variable {α : Type*}

/-- The steps of `a :: r` closed by `c`: either the closing step, or an inner step. -/
theorem witnessStepDescent_zip_cases {x y c : α} (r : List α) : ∀ (a : α),
    (x, y) ∈ List.zip (a :: r) (r ++ [c]) →
      (∃ u, a :: r = u ++ [x] ∧ y = c) ∨ ∃ s t, a :: r = s ++ x :: y :: t := by
  induction r with
  | nil =>
    intro a h
    simp only [List.nil_append, List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨hxa, hyc⟩ := Prod.mk.inj h
      exact Or.inl ⟨[], by rw [hxa, List.nil_append], hyc⟩
    · exact absurd h (by simp)
  | cons b r ih =>
    intro a h
    rw [List.cons_append, List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨hxa, hyb⟩ := Prod.mk.inj h
      exact Or.inr ⟨[], r, by rw [hxa, hyb, List.nil_append]⟩
    · rcases ih b h with ⟨u, hu, hyc⟩ | ⟨s, t, hst⟩
      · exact Or.inl ⟨a :: u, by rw [hu, List.cons_append], hyc⟩
      · exact Or.inr ⟨a :: s, t, by rw [hst, List.cons_append]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_zip_cases

/-- **A cyclic step of a list of length at least two is a rotation step.** -/
theorem witnessStepDescent_rotate_of_mem_steps {l : List α} {x y : α} (hl : 2 ≤ l.length)
    (h : (x, y) ∈ witnessStepDescent_steps l) :
    ∃ (n : ℕ) (s t : List α), l.rotate n = s ++ x :: y :: t := by
  cases l with
  | nil => exact absurd hl (by simp)
  | cons a r =>
    have hrot : (a :: r).rotate 1 = r ++ [a] := by simp
    unfold witnessStepDescent_steps at h
    rw [hrot] at h
    rw [List.length_cons] at hl
    rcases witnessStepDescent_zip_cases r a h with ⟨u, hu, hya⟩ | ⟨s, t, hst⟩
    · cases u with
      | nil =>
        have h1 := congrArg List.length hu
        rw [List.length_cons, List.nil_append, List.length_singleton] at h1
        omega
      | cons c u =>
        have hac : a = c := (List.cons.inj (hu.trans List.cons_append)).1
        refine ⟨(c :: u).length, [], u, ?_⟩
        rw [hu, List.rotate_append_length_eq, hya, hac, List.singleton_append,
          List.nil_append]
    · exact ⟨0, s, t, by rw [List.rotate_zero]; exact hst⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_rotate_of_mem_steps

/-- A list of steps without descents does not turn. -/
theorem witnessStepDescent_turnSum_eq_zero {f : α → ℕ} {N : ℕ} (ps : List (α × α))
    (h : ∀ p ∈ ps, f p.1 < f p.2) : witnessStepDescent_turnSum f N ps = 0 := by
  induction ps with
  | nil => rfl
  | cons q ps ih =>
    have ht : witnessStepDescent_turn f N q = 0 := if_pos (h q List.mem_cons_self)
    rw [witnessStepDescent_turnSum_cons, ih (fun p hp => h p (List.mem_cons_of_mem q hp)), ht]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turnSum_eq_zero

/-- **At most one descent turns at most once** (for a duplicate-free list of steps). -/
theorem witnessStepDescent_turnSum_le_of_unique {f : α → ℕ} {N : ℕ} (ps : List (α × α))
    (hnd : ps.Nodup)
    (h : ∀ p ∈ ps, ∀ q ∈ ps, ¬ f p.1 < f p.2 → ¬ f q.1 < f q.2 → p = q) :
    witnessStepDescent_turnSum f N ps ≤ N := by
  induction ps with
  | nil => exact Nat.zero_le N
  | cons q ps ih =>
    rw [witnessStepDescent_turnSum_cons]
    have hq : q ∉ ps := (List.nodup_cons.mp hnd).1
    by_cases hd : f q.1 < f q.2
    · have ht : witnessStepDescent_turn f N q = 0 := if_pos hd
      have := ih (List.nodup_cons.mp hnd).2 (fun p hp r hr =>
        h p (List.mem_cons_of_mem q hp) r (List.mem_cons_of_mem q hr))
      omega
    · have ht : witnessStepDescent_turn f N q = N := if_neg hd
      have h0 : witnessStepDescent_turnSum f N ps = 0 := by
        refine witnessStepDescent_turnSum_eq_zero ps fun p hp => ?_
        by_contra hp'
        have hpq := h p (List.mem_cons_of_mem q hp) q List.mem_cons_self hp' hd
        rw [hpq] at hp
        exact hq hp
      omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepDescent_turnSum_le_of_unique
