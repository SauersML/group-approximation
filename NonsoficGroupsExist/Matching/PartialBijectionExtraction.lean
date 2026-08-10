import NonsoficGroupsExist.Matching.PartialBijectionSwap

/-!
# Extracting a partial bijection from a permutation of a disjoint union

The points which a permutation carries from the left summand to the right
summand form the graph of a genuine partial bijection.  This construction is
the inverse of the swap encoding on swap involutions.
-/

namespace NonsoficGroupsExist
namespace FinitePartialBijection

variable {Y Z : FiniteModel}

/-- Left points which a permutation sends into the right summand. -/
noncomputable def crossingSource (p : Equiv.Perm (sumModel Y Z)) : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦ ∃ z : Z, p (Sum.inl y) = Sum.inr z

/-- Right points reached from the left summand by a permutation. -/
noncomputable def crossingTarget (p : Equiv.Perm (sumModel Y Z)) : Finset Z := by
  classical
  exact Finset.univ.filter fun z ↦ ∃ y : Y, p (Sum.inl y) = Sum.inr z

@[simp] theorem mem_crossingSource (p : Equiv.Perm (sumModel Y Z)) (y : Y) :
    y ∈ crossingSource p ↔ ∃ z : Z, p (Sum.inl y) = Sum.inr z := by
  classical
  simp [crossingSource]

@[simp] theorem mem_crossingTarget (p : Equiv.Perm (sumModel Y Z)) (z : Z) :
    z ∈ crossingTarget p ↔ ∃ y : Y, p (Sum.inl y) = Sum.inr z := by
  classical
  simp [crossingTarget]

/-- The right coordinate reached from a crossing source. -/
noncomputable def crossingValue (p : Equiv.Perm (sumModel Y Z))
    (y : Y) (hy : y ∈ crossingSource p) : Z :=
  Classical.choose ((mem_crossingSource p y).mp hy)

theorem crossingValue_spec (p : Equiv.Perm (sumModel Y Z))
    (y : Y) (hy : y ∈ crossingSource p) :
    p (Sum.inl y) = Sum.inr (crossingValue p y hy) :=
  Classical.choose_spec ((mem_crossingSource p y).mp hy)

/-- The left coordinate whose image is a crossing target. -/
noncomputable def crossingPreimage (p : Equiv.Perm (sumModel Y Z))
    (z : Z) (hz : z ∈ crossingTarget p) : Y :=
  Classical.choose ((mem_crossingTarget p z).mp hz)

theorem crossingPreimage_spec (p : Equiv.Perm (sumModel Y Z))
    (z : Z) (hz : z ∈ crossingTarget p) :
    p (Sum.inl (crossingPreimage p z hz)) = Sum.inr z :=
  Classical.choose_spec ((mem_crossingTarget p z).mp hz)

/-- The partial bijection formed by all left-to-right crossings of `p`. -/
noncomputable def extractCrossing (p : Equiv.Perm (sumModel Y Z)) :
    FinitePartialBijection Y Z where
  source := crossingSource p
  target := crossingTarget p
  equiv :=
    { toFun := fun y ↦
        ⟨crossingValue p y.1 y.2,
          (mem_crossingTarget p _).mpr
            ⟨y.1, crossingValue_spec p y.1 y.2⟩⟩
      invFun := fun z ↦
        ⟨crossingPreimage p z.1 z.2,
          (mem_crossingSource p _).mpr
            ⟨z.1, crossingPreimage_spec p z.1 z.2⟩⟩
      left_inv := by
        intro y
        apply Subtype.ext
        apply Sum.inl_injective
        apply p.injective
        rw [crossingPreimage_spec, crossingValue_spec]
      right_inv := by
        intro z
        apply Subtype.ext
        apply Sum.inr_injective
        rw [← crossingValue_spec, crossingPreimage_spec] }

@[simp] theorem extractCrossing_source (p : Equiv.Perm (sumModel Y Z)) :
    (extractCrossing p).source = crossingSource p := rfl

@[simp] theorem extractCrossing_target (p : Equiv.Perm (sumModel Y Z)) :
    (extractCrossing p).target = crossingTarget p := rfl

theorem extractCrossing_apply_spec (p : Equiv.Perm (sumModel Y Z))
    (y : Y) (hy : y ∈ (extractCrossing p).source) :
    p (Sum.inl y) = Sum.inr ((extractCrossing p).apply y hy) :=
  crossingValue_spec p y hy

theorem mem_extractCrossing_source_of_apply_eq
    (p : Equiv.Perm (sumModel Y Z)) (y : Y) (z : Z)
    (h : p (Sum.inl y) = Sum.inr z) : y ∈ (extractCrossing p).source :=
  (mem_crossingSource p y).mpr ⟨z, h⟩

theorem extractCrossing_apply_eq_of_apply_eq
    (p : Equiv.Perm (sumModel Y Z)) (y : Y) (z : Z)
    (h : p (Sum.inl y) = Sum.inr z) :
    (extractCrossing p).apply y
      (mem_extractCrossing_source_of_apply_eq p y z h) = z := by
  apply Sum.inr_injective
  rw [← h]
  exact (extractCrossing_apply_spec p y _).symm

/-- Extracting the crossing partial bijection from its swap involution
recovers the original partial bijection exactly. -/
@[simp] theorem extractCrossing_swapPerm (b : FinitePartialBijection Y Z) :
    extractCrossing b.swapPerm = b := by
  classical
  have hsource : (extractCrossing b.swapPerm).source = b.source := by
    ext y
    constructor
    · intro hy
      rw [extractCrossing_source, mem_crossingSource] at hy
      obtain ⟨z, hz⟩ := hy
      by_cases hsource : y ∈ b.source
      · exact hsource
      · rw [swapPerm_inl_of_not_mem b y hsource] at hz
        exact (Sum.inl_ne_inr hz).elim
    · intro hy
      rw [extractCrossing_source, mem_crossingSource]
      exact ⟨b.apply y hy, swapPerm_inl_of_mem b y hy⟩
  apply FinitePartialBijection.ext_source hsource
  intro y hy
  let hyb : y ∈ b.source := hsource ▸ hy
  have h := extractCrossing_apply_eq_of_apply_eq b.swapPerm y (b.apply y hyb)
    (swapPerm_inl_of_mem b y hyb)
  simpa only [proof_irrel_heq] using h

end FinitePartialBijection
end NonsoficGroupsExist
