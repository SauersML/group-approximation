import GroupApproximation.Matching.FinitePartialBijection
import GroupApproximation.Matching.BlockTransport
import GroupApproximation.Matching.DecompositionRefinement
import GroupApproximation.Matching.NormalizedComponents

/-!
# Partial bijections carried by component overlaps

For a permutation `q` and component blocks `C,D`, restriction of `q` to the
vertices of `C` landing in `D` is a concrete partial bijection from `C` to
`D`.  Its source and target cardinalities are exactly the overlap-matrix
entry.  This is the arrow carrier used by the finite cluster groupoid.
-/

namespace GroupApproximation

variable {Y : FiniteModel}

namespace BlockIndex

/-- Restriction of `q` from `C` to the part of its image lying in `D`. -/
noncomputable def overlapPartialBijection (P : BlockStructure Y)
    (q : Equiv.Perm Y) (C D : BlockIndex P) :
    FinitePartialBijection (indexedBlockModel P C) (indexedBlockModel P D) where
  source := Finset.univ.filter fun x ↦ q x.1 ∈ D.block
  target := Finset.univ.filter fun y ↦ q⁻¹ y.1 ∈ C.block
  equiv :=
    { toFun := fun x ↦
        ⟨⟨q x.1.1, (Finset.mem_filter.mp x.2).2⟩, by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          change q⁻¹ (q x.1.1) ∈ C.block
          have heq : q⁻¹ (q x.1.1) = x.1.1 := by
            rw [Equiv.Perm.coe_inv]
            exact q.symm_apply_apply _
          rw [heq]
          exact x.1.2⟩
      invFun := fun y ↦
        ⟨⟨q⁻¹ y.1.1, (Finset.mem_filter.mp y.2).2⟩, by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          change q (q⁻¹ y.1.1) ∈ D.block
          have heq : q (q⁻¹ y.1.1) = y.1.1 := by
            change q (q.symm y.1.1) = y.1.1
            exact q.apply_symm_apply _
          rw [heq]
          exact y.1.2⟩
      left_inv := fun x ↦ by ext; simp
      right_inv := fun y ↦ by ext; simp }

@[simp] theorem overlapPartialBijection_apply (P : BlockStructure Y)
    (q : Equiv.Perm Y) (C D : BlockIndex P)
    (x : indexedBlockModel P C)
    (hx : x ∈ (overlapPartialBijection P q C D).source) :
    (overlapPartialBijection P q C D).apply x hx = q x.1 := rfl

/-- The source size of the overlap partial bijection is the overlap entry. -/
theorem card_overlapPartialBijection_source (P : BlockStructure Y)
    (q : Equiv.Perm Y) (C D : BlockIndex P) :
    (overlapPartialBijection P q C D).source.card = overlap P q C D := by
  classical
  unfold overlapPartialBijection overlap
  apply Finset.card_bij (fun x _ ↦ q x.1)
  · intro x hx
    rw [Finset.mem_inter]
    exact ⟨Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩,
      (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext (q.injective hxy)
  · intro y hy
    obtain ⟨hyqC, hyD⟩ := Finset.mem_inter.mp hy
    obtain ⟨x, hxC, hxy⟩ := Finset.mem_image.mp hyqC
    refine ⟨⟨x, hxC⟩, ?_, hxy⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hxy ▸ hyD⟩

/-- The target size is the same overlap entry. -/
theorem card_overlapPartialBijection_target (P : BlockStructure Y)
    (q : Equiv.Perm Y) (C D : BlockIndex P) :
    (overlapPartialBijection P q C D).target.card = overlap P q C D := by
  rw [(overlapPartialBijection P q C D).card_source_eq_card_target.symm]
  exact card_overlapPartialBijection_source P q C D

end BlockIndex

namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- The overlap arrow from a component to its chosen dominant target. -/
noncomputable def refinementPartialBijection (q : Equiv.Perm (S.model n))
    (C : D.componentIndex n) :
    FinitePartialBijection (indexedBlockModel (D.blocks n) C)
      (indexedBlockModel (D.blocks n) (D.refineIndex q C)) :=
  BlockIndex.overlapPartialBijection (D.blocks n) q C (D.refineIndex q C)

/-- Its missing source mass is exactly the existing component-leakage
quantity. -/
theorem refinementPartialBijection_sourceDefect
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    (D.refinementPartialBijection q C).sourceDefect =
      D.componentLeakage (D.blocks n) q C := by
  have hsplit := D.overlap_refineIndex_add_componentLeakage q C
  rw [refinementPartialBijection, FinitePartialBijection.sourceDefect,
    BlockIndex.card_overlapPartialBijection_source]
  simp only [Fintype.card_coe]
  omega

/-- Source and range defects coincide for a partial bijection between the two
selected component blocks. -/
theorem refinementPartialBijection_targetDefect
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    (D.refinementPartialBijection q C).targetDefect =
      (D.refineIndex q C).block.card -
        BlockIndex.overlap (D.blocks n) q C (D.refineIndex q C) := by
  rw [refinementPartialBijection, FinitePartialBijection.targetDefect,
    BlockIndex.card_overlapPartialBijection_target]
  simp only [Fintype.card_coe]

/-- On a reciprocal component for an exact involution, the range defect of
the overlap arrow is exactly the leakage of its target component. -/
theorem refinementPartialBijection_targetDefect_of_involution
    (q : Equiv.Perm (S.model n)) (hsq : q * q = 1)
    (C : D.componentIndex n)
    (hrecip : D.refineIndex q (D.refineIndex q C) = C) :
    (D.refinementPartialBijection q C).targetDefect =
      D.componentLeakage (D.blocks n) q (D.refineIndex q C) := by
  let E := D.refineIndex q C
  have hsplit := D.overlap_refineIndex_add_componentLeakage q E
  have hchosen : D.refineIndex q E = C := by
    simpa [E] using hrecip
  rw [hchosen] at hsplit
  have hsymm := BlockIndex.overlap_comm_of_sq (D.blocks n) q hsq C E
  rw [D.refinementPartialBijection_targetDefect q C]
  change E.block.card - BlockIndex.overlap (D.blocks n) q C E =
    D.componentLeakage (D.blocks n) q E
  rw [hsymm]
  omega

/-- For an exact inverse pair, reciprocity identifies the range defect of the
`q` overlap arrow with the one-sided leakage of the inverse arrow at its
target component. -/
theorem refinementPartialBijection_targetDefect_of_inverse
    (q r : Equiv.Perm (S.model n)) (hr : r = q⁻¹)
    (C : D.componentIndex n)
    (hrecip : D.refineIndex r (D.refineIndex q C) = C) :
    (D.refinementPartialBijection q C).targetDefect =
      D.componentLeakage (D.blocks n) r (D.refineIndex q C) := by
  subst r
  let E := D.refineIndex q C
  have hsplit := D.overlap_refineIndex_add_componentLeakage q⁻¹ E
  have hchosen : D.refineIndex q⁻¹ E = C := by
    simpa [E] using hrecip
  rw [hchosen] at hsplit
  have hreverse := BlockIndex.overlap_inv_comm (D.blocks n) q C E
  rw [D.refinementPartialBijection_targetDefect q C]
  change E.block.card - BlockIndex.overlap (D.blocks n) q C E =
    D.componentLeakage (D.blocks n) q⁻¹ E
  rw [hreverse]
  omega

end ExpanderDecomposition
end GroupApproximation
