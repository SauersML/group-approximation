import GroupApproximation.Higman.CentralHNNFreeLabelAffineSubgroup

/-!
# Alphabet form of affine coordinate subgroups

When the inserted subgroup is a coordinate subgroup of a free group, the
whole affine orbit subgroup is again a coordinate subgroup.  Its alphabet is
the union of the labels met by the base subgroup and all right translates of
the inserted alphabet.
-/

namespace GroupApproximation
namespace Higman
namespace CentralHNNFreeLabel

variable {G : Type} [Group G] (M : Subgroup G)

/-- Labels intrinsic to `S`, together with the complete `S`-orbit of `T`. -/
def affineLabelSet
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (S : Subgroup G) (T : Set (Label M d)) : Set (Label M d) :=
  labelSet M d S ∪
    {q | ∃ g : G, g ∈ S ∧ ∃ r : Label M d,
      r ∈ T ∧ q = rightLabel (M := M) d g r}

/-- The affine orbit of a coordinate subgroup is the coordinate subgroup on
the affine orbit of its alphabet. -/
theorem affineCoordSub_closure_eq
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (S : Subgroup G) (T : Set (Label M d)) :
    affineCoordSub M d S (Subgroup.closure (FreeGroup.of '' T)) =
      Subgroup.closure (FreeGroup.of '' affineLabelSet M d S T) := by
  apply le_antisymm
  · rw [affineCoordSub, Subgroup.closure_le]
    intro w hw
    rcases hw with hw | hw
    · obtain ⟨q, hq, rfl⟩ := hw
      apply Subgroup.subset_closure
      exact ⟨q, Or.inl hq, rfl⟩
    · obtain ⟨g, hg, v, hv, rfl⟩ := hw
      refine Subgroup.closure_induction
        (p := fun v _ => FreeGroup.map (rightLabel (M := M) d g) v ∈
          Subgroup.closure (FreeGroup.of '' affineLabelSet M d S T))
        ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨q, hq, rfl⟩
        rw [FreeGroup.map.of]
        apply Subgroup.subset_closure
        exact ⟨rightLabel (M := M) d g q,
          Or.inr ⟨g, hg, q, hq, rfl⟩, rfl⟩
      · rw [map_one]
        exact Subgroup.one_mem _
      · intro x y _ _ hx hy
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
      · intro x _ hx
        rw [map_inv]
        exact Subgroup.inv_mem _ hx
  · rw [Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    apply Subgroup.subset_closure
    rcases hq with hq | hq
    · left
      exact ⟨q, hq, rfl⟩
    · obtain ⟨g, hg, r, hr, rfl⟩ := hq
      right
      refine ⟨g, hg, FreeGroup.of r, ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨r, hr, rfl⟩
      · rw [FreeGroup.map.of]

/-- Intersecting an affine coordinate subgroup with another coordinate
subgroup reduces exactly to intersecting their alphabets. -/
theorem affineCoordSub_inf_closure_le
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (S : Subgroup G) (T R : Set (Label M d)) :
    affineCoordSub M d S (Subgroup.closure (FreeGroup.of '' T)) ⊓
        Subgroup.closure (FreeGroup.of '' R) ≤
      Subgroup.closure (FreeGroup.of '' (affineLabelSet M d S T ∩ R)) := by
  rw [affineCoordSub_closure_eq]
  exact Coordinate.closure_inter_le (affineLabelSet M d S T) R

end CentralHNNFreeLabel
end Higman
end GroupApproximation
