import NonsoficGroupsExist.Matching.FinitePartialBijection

/-!
# Encoding a partial bijection by an involution

A partial bijection between finite models is the same data as an involution
of their disjoint union which swaps every matched pair and fixes every
unmatched point.  This converts partial-arrow composition questions into
ordinary finite permutation questions.
-/

namespace NonsoficGroupsExist
namespace FinitePartialBijection

variable {Y Z W : FiniteModel}

/-- Disjoint union of two finite models. -/
abbrev sumModel (Y Z : FiniteModel) : FiniteModel where
  carrier := Y ⊕ Z
  fintype := by
    letI : Fintype Y.carrier := Y.fintype
    letI : Fintype Z.carrier := Z.fintype
    exact inferInstance
  decidableEq := by
    letI : DecidableEq Y.carrier := Y.decidableEq
    letI : DecidableEq Z.carrier := Z.decidableEq
    exact inferInstance

/-- The involution which swaps the graph pairs of `b` and fixes all
unmatched points. -/
def swapPerm (b : FinitePartialBijection Y Z) :
    Equiv.Perm (sumModel Y Z) where
  toFun
    | Sum.inl y => if hy : y ∈ b.source then Sum.inr (b.apply y hy) else Sum.inl y
    | Sum.inr z => if hz : z ∈ b.target then Sum.inl (b.symm.apply z hz) else Sum.inr z
  invFun
    | Sum.inl y => if hy : y ∈ b.source then Sum.inr (b.apply y hy) else Sum.inl y
    | Sum.inr z => if hz : z ∈ b.target then Sum.inl (b.symm.apply z hz) else Sum.inr z
  left_inv := by
    intro x
    cases x with
    | inl y =>
        by_cases hy : y ∈ b.source
        · simp only [hy, dite_true]
          rw [dif_pos (b.apply_mem_target y hy)]
          simp
        · simp [hy]
    | inr z =>
        by_cases hz : z ∈ b.target
        · simp only [hz, dite_true]
          have hy : b.symm.apply z hz ∈ b.source :=
            b.symm.apply_mem_target z hz
          rw [dif_pos hy]
          exact congrArg Sum.inr (b.apply_symm_apply z hz)
        · simp [hz]
  right_inv := by
    intro x
    cases x with
    | inl y =>
        by_cases hy : y ∈ b.source
        · simp only [hy, dite_true]
          rw [dif_pos (b.apply_mem_target y hy)]
          simp
        · simp [hy]
    | inr z =>
        by_cases hz : z ∈ b.target
        · simp only [hz, dite_true]
          have hy : b.symm.apply z hz ∈ b.source :=
            b.symm.apply_mem_target z hz
          rw [dif_pos hy]
          exact congrArg Sum.inr (b.apply_symm_apply z hz)
        · simp [hz]

@[simp] theorem swapPerm_inl_of_mem
    (b : FinitePartialBijection Y Z) (y : Y) (hy : y ∈ b.source) :
    b.swapPerm (Sum.inl y) = Sum.inr (b.apply y hy) := by
  simp [swapPerm, hy]

@[simp] theorem swapPerm_inl_of_not_mem
    (b : FinitePartialBijection Y Z) (y : Y) (hy : y ∉ b.source) :
    b.swapPerm (Sum.inl y) = Sum.inl y := by
  simp [swapPerm, hy]

@[simp] theorem swapPerm_inr_of_mem
    (b : FinitePartialBijection Y Z) (z : Z) (hz : z ∈ b.target) :
    b.swapPerm (Sum.inr z) = Sum.inl (b.symm.apply z hz) := by
  simp [swapPerm, hz]

@[simp] theorem swapPerm_inr_of_not_mem
    (b : FinitePartialBijection Y Z) (z : Z) (hz : z ∉ b.target) :
    b.swapPerm (Sum.inr z) = Sum.inr z := by
  simp [swapPerm, hz]

theorem swapPerm_mul_self (b : FinitePartialBijection Y Z) :
    b.swapPerm * b.swapPerm = 1 := by
  apply Equiv.ext
  intro x
  exact b.swapPerm.left_inv x

/-- Embed the swap of `Y` and `Z` into the three-layer model
`Y ⊕ (Z ⊕ W)`, fixing `W`. -/
def firstSwap (b : FinitePartialBijection Y Z) :
    Equiv.Perm (sumModel Y (sumModel Z W)) :=
  (Equiv.sumAssoc Y Z W).symm |>.trans
    (Equiv.sumCongr b.swapPerm (Equiv.refl W)) |>.trans
    (Equiv.sumAssoc Y Z W)

/-- Embed the swap of `Z` and `W` into the three-layer model, fixing `Y`. -/
def secondSwap (c : FinitePartialBijection Z W) :
    Equiv.Perm (sumModel Y (sumModel Z W)) :=
  Equiv.sumCongr (Equiv.refl Y) c.swapPerm

@[simp] theorem firstSwap_inl_of_mem
    (b : FinitePartialBijection Y Z) (y : Y) (hy : y ∈ b.source) :
    (firstSwap (W := W) b) (Sum.inl y) = Sum.inr (Sum.inl (b.apply y hy)) := by
  rw [firstSwap, Equiv.trans_apply, Equiv.trans_apply]
  change (Equiv.sumAssoc Y Z W)
    (Sum.inl (b.swapPerm (Sum.inl y))) = _
  rw [swapPerm_inl_of_mem b y hy]
  rfl

@[simp] theorem secondSwap_middle_of_mem
    (c : FinitePartialBijection Z W) (z : Z) (hz : z ∈ c.source) :
    (secondSwap (Y := Y) c) (Sum.inr (Sum.inl z)) =
      Sum.inr (Sum.inr (c.apply z hz)) := by
  change Sum.inr (c.swapPerm (Sum.inl z)) = _
  rw [swapPerm_inl_of_mem c z hz]

/-- On every composable source point, the product of the two swaps carries
the first layer to the third layer by the partial composite. -/
theorem secondSwap_mul_firstSwap_apply
    (b : FinitePartialBijection Y Z) (c : FinitePartialBijection Z W)
    (y : Y) (hy : y ∈ (b.trans c).source) :
    (secondSwap (Y := Y) c * firstSwap (W := W) b) (Sum.inl y) =
      Sum.inr (Sum.inr ((b.trans c).apply y hy)) := by
  obtain ⟨hyb, hyc⟩ := (b.mem_trans_source c y).mp hy
  rw [Equiv.Perm.mul_apply, firstSwap_inl_of_mem b y hyb,
    secondSwap_middle_of_mem c (b.apply y hyb) hyc]
  rfl

end FinitePartialBijection
end NonsoficGroupsExist
