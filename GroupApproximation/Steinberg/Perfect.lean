import GroupApproximation.Steinberg.Basic

/-!
# Perfectness of Steinberg groups

In rank at least three, every root generator is a single commutator through
a third index.  Since the root generators generate the presented group,
this proves perfectness directly from the Steinberg relations.
-/

namespace GroupApproximation
namespace SteinbergGroup

open scoped commutatorElement

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- A Steinberg group is perfect whenever every ordered pair of distinct
indices admits a third index distinct from both. -/
theorem isPerfect_of_exists_third
    (hthird : ∀ i j : I, i ≠ j → ∃ k : I, k ≠ i ∧ k ≠ j) :
    Group.IsPerfect (SteinbergGroup I R) := by
  refine ⟨?_⟩
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by (relations (I := I) (R := R))
      (commutator (SteinbergGroup I R)) ?_ g
  rintro ⟨i, j, hij, a⟩
  obtain ⟨k, hki, hkj⟩ := hthird i j hij
  have hik : i ≠ k := Ne.symm hki
  have hcomm :
      ⁅x i k hik a, x k j hkj 1⁆ = x i j hij a := by
    simpa using x_commutator i k j hik hkj hij a 1
  change x i j hij a ∈ commutator (SteinbergGroup I R)
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- `St_n(R)` is perfect for `n ≥ 3`. -/
theorem fin_isPerfect {n : ℕ} (hn : 3 ≤ n) :
    Group.IsPerfect (SteinbergGroup (Fin n) R) := by
  apply isPerfect_of_exists_third
  intro i j _
  exact Fin.exists_ne_and_ne_of_two_lt i j (by omega)

end SteinbergGroup
end GroupApproximation
