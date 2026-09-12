import GroupApproximation.Matching.DecompositionRefinement

/-!
# Repairing an almost-involutive component map

For any self-map `f`, keep `f i` where `f (f i) = i` and fix `i` elsewhere.
The resulting map is an exact involutive permutation.  Applied to dominant
component targets, its changed weighted mass is bounded by the existing
nonreciprocal-component mass.
-/

namespace GroupApproximation

/-- Keep an already reciprocal pair and fix every nonreciprocal point. -/
noncomputable def involutionRepairFun {I : Type*} (f : I → I) (i : I) : I := by
  classical
  exact if f (f i) = i then f i else i

theorem involutionRepairFun_apply_of_good {I : Type*} (f : I → I) (i : I)
    (hi : f (f i) = i) : involutionRepairFun f i = f i := by
  simp [involutionRepairFun, hi]

theorem involutionRepairFun_apply_of_bad {I : Type*} (f : I → I) (i : I)
    (hi : f (f i) ≠ i) : involutionRepairFun f i = i := by
  simp [involutionRepairFun, hi]

theorem involutionRepairFun_involutive {I : Type*} (f : I → I) (i : I) :
    involutionRepairFun f (involutionRepairFun f i) = i := by
  classical
  by_cases hi : f (f i) = i
  · simp [involutionRepairFun, hi]
  · simp [involutionRepairFun, hi]

/-- The repaired self-map as an exact permutation. -/
noncomputable def involutionRepair {I : Type*} (f : I → I) : Equiv.Perm I where
  toFun := involutionRepairFun f
  invFun := involutionRepairFun f
  left_inv := involutionRepairFun_involutive f
  right_inv := involutionRepairFun_involutive f

@[simp] theorem involutionRepair_apply {I : Type*} (f : I → I) (i : I) :
    involutionRepair f i = involutionRepairFun f i := rfl

theorem involutionRepair_mul_self {I : Type*} (f : I → I) :
    involutionRepair f * involutionRepair f = 1 := by
  ext i
  exact involutionRepairFun_involutive f i

namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- Exact involutive repair of the dominant-target component map. -/
noncomputable def repairedComponentInvolution
    (q : Equiv.Perm (S.model n)) : Equiv.Perm (D.componentIndex n) :=
  involutionRepair (D.refineIndex q)

theorem repairedComponentInvolution_eq_refineIndex_of_reciprocal
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n)
    (hC : D.refineIndex q (D.refineIndex q C) = C) :
    D.repairedComponentInvolution q C = D.refineIndex q C := by
  exact involutionRepairFun_apply_of_good _ _ hC

theorem repairedComponentInvolution_eq_self_of_nonreciprocal
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n)
    (hC : D.refineIndex q (D.refineIndex q C) ≠ C) :
    D.repairedComponentInvolution q C = C := by
  exact involutionRepairFun_apply_of_bad _ _ hC

theorem repairedComponentInvolution_mul_self
    (q : Equiv.Perm (S.model n)) :
    D.repairedComponentInvolution q * D.repairedComponentInvolution q = 1 :=
  involutionRepair_mul_self _

/-- Components on which repair changes the dominant target lie in the
nonreciprocal locus. -/
theorem repairedComponentInvolution_changed_subset
    (q : Equiv.Perm (S.model n)) :
    (Finset.univ.filter fun C : D.componentIndex n ↦
      D.repairedComponentInvolution q C ≠ D.refineIndex q C) ⊆
      D.nonreciprocal q := by
  classical
  intro C hC
  rw [Finset.mem_filter] at hC
  rw [nonreciprocal, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hrecip
  exact hC.2 (D.repairedComponentInvolution_eq_refineIndex_of_reciprocal
    q C hrecip)

/-- The total vertex mass of changed components is at most the existing
nonreciprocal mass. -/
theorem repairedComponentInvolution_changedMass_le
    (q : Equiv.Perm (S.model n)) :
    (∑ C ∈ Finset.univ.filter (fun C : D.componentIndex n ↦
      D.repairedComponentInvolution q C ≠ D.refineIndex q C),
        (C.block.card : ℝ)) ≤ D.nonreciprocalMass q := by
  unfold nonreciprocalMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (D.repairedComponentInvolution_changed_subset q) (fun _ _ _ ↦ by positivity)

end ExpanderDecomposition
end GroupApproximation
