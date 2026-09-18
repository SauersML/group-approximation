import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Code.GenIndex
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

/-!
# The defining relators of `G(M)` form a finite set

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, in the
form of the coding step for the Kharlampovich group `KMS.KhGroup M`.

Each relator family G1--G8 of KMS Sec. 4.1 is indexed by a finite type
(tuples of states, subsets of `{0, …, K}`, letters, and `α : Fin K → Fin 3`),
or, for G8, by the program of `M`. So `KMS.relators M` is finite.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

variable {K N : ℕ}

/-- A relator family covered by the range of a map from a finite type is finite. -/
theorem finite_of_forall_exists_eq {ι : Type*} [Finite ι] {s : Set (FreeGroup (KhGen K N))}
    (f : ι → FreeGroup (KhGen K N)) (h : ∀ r ∈ s, ∃ i, f i = r) : s.Finite := by
  refine (Set.finite_range f).subset ?_
  intro r hr
  exact h r hr

theorem g1Relators_finite (K N : ℕ) : (g1Relators K N).Finite := by
  unfold g1Relators
  refine Set.Finite.union (Set.Finite.union (Set.Finite.union (Set.Finite.union ?_ ?_) ?_) ?_) ?_
  · exact finite_of_forall_exists_eq
      (fun q : Fin (N + 1) × Finset (Fin (K + 1)) ↦ (gx q.1 q.2 ^ 2 : FreeGroup (KhGen K N)))
      (by rintro r ⟨j, S, rfl⟩; exact ⟨(j, S), rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun q : Fin (N + 1) × Fin (N + 1) × Finset (Fin (K + 1)) × Finset (Fin (K + 1)) ↦
        (khComm (gx q.1 q.2.2.1) (gx q.2.1 q.2.2.2) : FreeGroup (KhGen K N)))
      (by rintro r ⟨j, j', S, S', rfl⟩; exact ⟨(j, j', S, S'), rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun i : Fin (K + 1) ↦ (gA i ^ 2 : FreeGroup (KhGen K N)))
      (by rintro r ⟨i, rfl⟩; exact ⟨i, rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun q : Fin (K + 1) × Fin (K + 1) ↦
        (khComm (gA q.1) (gA q.2) : FreeGroup (KhGen K N)))
      (by rintro r ⟨i, i', rfl⟩; exact ⟨(i, i'), rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun q : KhGen K N × KhGen K N ↦
        (khComm (FreeGroup.of q.1) (FreeGroup.of q.2) : FreeGroup (KhGen K N)))
      (by rintro r ⟨s, t, -, -, rfl⟩; exact ⟨(s, t), rfl⟩)

theorem g2Relators_finite (K N : ℕ) : (g2Relators K N).Finite :=
  finite_of_forall_exists_eq
    (fun q : KhGen K N × KhGen K N ↦
      (khComm (FreeGroup.of q.1) (FreeGroup.of q.2) : FreeGroup (KhGen K N)))
    (by rintro r ⟨s, t, _, _, -, -, -, rfl⟩; exact ⟨(s, t), rfl⟩)

theorem g3Relators_finite (K N : ℕ) : (g3Relators K N).Finite := by
  unfold g3Relators
  refine Set.Finite.union (Set.Finite.union ?_ ?_) ?_
  · exact finite_of_forall_exists_eq
      (fun n : Fin K ↦ (khConj (gA n.succ) (ga n)⁻¹ * (gA n.succ)⁻¹ *
        (khConj (gA n.succ) (ga' n)⁻¹)⁻¹ : FreeGroup (KhGen K N)))
      (by rintro r ⟨n, rfl⟩; exact ⟨n, rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun n : Fin K ↦
        (khComm (khConj (gA n.succ) (ga n)) (gA n.succ) : FreeGroup (KhGen K N)))
      (by rintro r ⟨n, rfl⟩; exact ⟨n, rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun n : Fin K ↦
        (khComm (khConj (gA n.succ) (ga n)⁻¹) (gA n.succ) : FreeGroup (KhGen K N)))
      (by rintro r ⟨n, rfl⟩; exact ⟨n, rfl⟩)

theorem g4Relators_finite (K N : ℕ) : (g4Relators K N).Finite := by
  unfold g4Relators
  refine Set.Finite.union ?_ ?_
  · exact finite_of_forall_exists_eq
      (fun n : Fin K ↦ (khConj (gA 0) (gta n)⁻¹ * (gA 0)⁻¹ *
        (khConj (gA 0) (gta' n)⁻¹)⁻¹ : FreeGroup (KhGen K N)))
      (by rintro r ⟨n, rfl⟩; exact ⟨n, rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun α : Fin K → Fin 3 ↦
        (khComm (khConj (gA 0) (zword gta α)) (gA 0) : FreeGroup (KhGen K N)))
      (by rintro r ⟨α, rfl⟩; exact ⟨α, rfl⟩)

theorem g5aRelators_finite (K N : ℕ) : (g5aRelators K N).Finite :=
  finite_of_forall_exists_eq
    (fun q : Fin (N + 1) × Finset (Fin (K + 1)) × Fin (K + 1) ↦
      (khComm (gx q.1 q.2.1) (gA q.2.2) * (gx q.1 (insert q.2.2 q.2.1))⁻¹ :
        FreeGroup (KhGen K N)))
    (by rintro r ⟨j, S, i, -, rfl⟩; exact ⟨(j, S, i), rfl⟩)

theorem g5bRelators_finite (K N : ℕ) : (g5bRelators K N).Finite :=
  finite_of_forall_exists_eq
    (fun q : Fin (N + 1) × Finset (Fin (K + 1)) × Fin K ↦
      (khConj (gx q.1 q.2.1) (ga q.2.2) * (gx q.1 q.2.1)⁻¹ *
        (khConj (gx q.1 q.2.1) (ga' q.2.2))⁻¹ : FreeGroup (KhGen K N)))
    (by rintro r ⟨j, S, n, -, rfl⟩; exact ⟨(j, S, n), rfl⟩)

theorem g5cRelators_finite (K N : ℕ) : (g5cRelators K N).Finite :=
  finite_of_forall_exists_eq
    (fun q : Fin (N + 1) × Finset (Fin (K + 1)) × KhGen K N ↦
      (khComm (gx q.1 q.2.1) (FreeGroup.of q.2.2) : FreeGroup (KhGen K N)))
    (by rintro r ⟨j, S, s, _, -, -, rfl⟩; exact ⟨(j, S, s), rfl⟩)

theorem g6Relators_finite (K N : ℕ) : (g6Relators K N).Finite := by
  unfold g6Relators
  refine Set.Finite.union ?_ ?_
  · exact finite_of_forall_exists_eq
      (fun q : Fin (N + 1) × Fin K ↦
        (khConj (gx q.1 ∅) (ga q.2) * (khConj (gx q.1 ∅) (gta q.2))⁻¹ :
          FreeGroup (KhGen K N)))
      (by rintro r ⟨j, n, rfl⟩; exact ⟨(j, n), rfl⟩)
  · exact finite_of_forall_exists_eq
      (fun q : Fin (N + 1) × Fin K ↦
        (khConj (gx q.1 ∅) (ga' q.2) * (khConj (gx q.1 ∅) (gta' q.2))⁻¹ :
          FreeGroup (KhGen K N)))
      (by rintro r ⟨j, n, rfl⟩; exact ⟨(j, n), rfl⟩)

theorem g7Relators_finite (K N : ℕ) : (g7Relators K N).Finite :=
  finite_of_forall_exists_eq
    (fun q : Fin (N + 1) × Fin (N + 1) × Finset (Fin (K + 1)) × Finset (Fin (K + 1)) ×
        (Fin K → Fin 3) ↦
      (khComm (khConj (gx q.1 q.2.2.1) (zword ga q.2.2.2.2)) (gx q.2.1 q.2.2.2.1) :
        FreeGroup (KhGen K N)))
    (by rintro r ⟨j, j', S, S', α, rfl⟩; exact ⟨(j, j', S, S', α), rfl⟩)

theorem machineRelators_finite (M : Minsky.Machine K N) : (machineRelators M).Finite := by
  refine ((List.finite_toSet M.prog).image instrRelator).subset ?_
  rintro r ⟨c, hc, rfl⟩
  exact ⟨c, hc, rfl⟩

/-- The defining relators G1--G8 of `G(M)` form a finite set. -/
theorem relators_finite (M : Minsky.Machine K N) : (relators M).Finite :=
  ((((((((((g1Relators_finite K N).union (g2Relators_finite K N)).union
    (g3Relators_finite K N)).union (g4Relators_finite K N)).union
    (g5aRelators_finite K N)).union (g5bRelators_finite K N)).union
    (g5cRelators_finite K N)).union (g6Relators_finite K N)).union
    (g7Relators_finite K N)).union (machineRelators_finite M))

end KMS

end GroupApproximation.Full.Kharlampovich
