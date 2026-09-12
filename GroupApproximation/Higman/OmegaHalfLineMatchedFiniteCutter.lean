import GroupApproximation.Higman.OmegaHalfLineLabelShift

/-!
# A shared finite cutter for the one-sided Omega edge

The global label shift lets the source witness be reused on the target side.
The finite ambient and cutter do not change: only the embedding of the free
label group is precomposed with the inverse shift.  On the common abstract
right-tail basis the source and target embeddings are then literally equal.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The global label permutation carries the source distinguished set exactly
onto the inserted target distinguished set. -/
theorem rightTailLabelShiftEquiv_image (m : ℕ) (beta : E) :
    rightTailLabelShiftEquiv m beta '' rightTailLabel m =
      insertedRightTailLabel m beta := by
  ext q
  constructor
  · rintro ⟨q₀, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨beta + l, ⟨l, hl, rfl⟩, ?_⟩
    exact (rightTailLabelShiftEquiv_apply m beta ⟨l, hl⟩).symm
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨bK l, ⟨l, hl, rfl⟩, ?_⟩
    exact rightTailLabelShiftEquiv_apply m beta ⟨l, hl⟩

/-- Consequently the induced free-group automorphism carries the source
coordinate subgroup exactly onto the target coordinate subgroup. -/
theorem map_rightTailCoord_matchedFreeShift
    (m : ℕ) (beta : E) :
    (Star.coordSub (rightTailLabel m)).map
        (rightTailFreeShiftEquiv m beta).toMonoidHom =
      Star.coordSub (insertedRightTailLabel m beta) := by
  unfold Star.coordSub
  rw [MonoidHom.map_closure]
  congr 1
  have hgen :
      (rightTailFreeShiftEquiv m beta).toMonoidHom ''
          (FreeGroup.of '' rightTailLabel m) =
        FreeGroup.of ''
          (rightTailLabelShiftEquiv m beta '' rightTailLabel m) := by
    ext w
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨rightTailLabelShiftEquiv m beta q,
        ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨FreeGroup.of q, ⟨q, hq, rfl⟩, rfl⟩
  rw [hgen, rightTailLabelShiftEquiv_image]

/-- Pulling the source coordinate subgroup back along the inverse shift is
exactly the target coordinate subgroup. -/
theorem comap_rightTailCoord_rightTailFreeShiftEquiv_symm
    (m : ℕ) (beta : E) :
    (Star.coordSub (rightTailLabel m)).comap
        (rightTailFreeShiftEquiv m beta).symm.toMonoidHom =
      Star.coordSub (insertedRightTailLabel m beta) := by
  apply le_antisymm
  · intro w hw
    have hmap : rightTailFreeShiftEquiv m beta
        ((rightTailFreeShiftEquiv m beta).symm w) ∈
          (Star.coordSub (rightTailLabel m)).map
            (rightTailFreeShiftEquiv m beta).toMonoidHom :=
      ⟨(rightTailFreeShiftEquiv m beta).symm w, hw, rfl⟩
    rw [map_rightTailCoord_matchedFreeShift] at hmap
    simpa using hmap
  · intro w hw
    rw [← map_rightTailCoord_matchedFreeShift m beta] at hw
    obtain ⟨v, hv, hvw⟩ := hw
    change (rightTailFreeShiftEquiv m beta).symm w ∈
      Star.coordSub (rightTailLabel m)
    rw [← hvw]
    change (rightTailFreeShiftEquiv m beta).symm
      (rightTailFreeShiftEquiv m beta v) ∈ _
    rw [MulEquiv.symm_apply_apply]
    exact hv

/-- The single finite ambient used for both sides of the matched cutter. -/
abbrev rightTailMatchedAmbient (m : ℕ) : Type :=
  (rightTailPairedEqualizerWitness m).witness.K

/-- Source embedding into the shared finite ambient. -/
noncomputable def rightTailMatchedSourceEmb (m : ℕ) :
    FreeGroup ↥Conj.K →* rightTailMatchedAmbient m :=
  (rightTailPairedEqualizerWitness m).witness.emb

/-- Target embedding into the same ambient, obtained by pulling labels back
through the global shift. -/
noncomputable def rightTailMatchedTargetEmb (m : ℕ) (beta : E) :
    FreeGroup ↥Conj.K →* rightTailMatchedAmbient m :=
  (rightTailMatchedSourceEmb m).comp
    (rightTailFreeShiftEquiv m beta).symm.toMonoidHom

theorem rightTailMatchedSourceEmb_injective (m : ℕ) :
    Function.Injective (rightTailMatchedSourceEmb m) :=
  (rightTailPairedEqualizerWitness m).witness.emb_injective

theorem rightTailMatchedTargetEmb_injective (m : ℕ) (beta : E) :
    Function.Injective (rightTailMatchedTargetEmb m beta) :=
  (rightTailMatchedSourceEmb_injective m).comp
    (rightTailFreeShiftEquiv m beta).symm.injective

/-- The source side is cut out exactly by the shared finitely generated
cutter. -/
theorem rightTailMatchedCutter_comap_source (m : ℕ) :
    (rightTailPairedEqualizerWitness m).witness.L.comap
        (rightTailMatchedSourceEmb m) =
      Star.coordSub (rightTailLabel m) :=
  (rightTailPairedEqualizerWitness m).witness.comap_eq

/-- The very same finite cutter cuts out the inserted target under the target
embedding. -/
theorem rightTailMatchedCutter_comap_target (m : ℕ) (beta : E) :
    (rightTailPairedEqualizerWitness m).witness.L.comap
        (rightTailMatchedTargetEmb m beta) =
      Star.coordSub (insertedRightTailLabel m beta) := by
  change ((rightTailPairedEqualizerWitness m).witness.L.comap
      (rightTailMatchedSourceEmb m)).comap
        (rightTailFreeShiftEquiv m beta).symm.toMonoidHom = _
  rw [rightTailMatchedCutter_comap_source,
    comap_rightTailCoord_rightTailFreeShiftEquiv_symm]

/-- On the common abstract right-tail free basis, inverse-shifted target
evaluation is exactly source evaluation. -/
theorem rightTailFreeShiftEquiv_symm_comp_inserted (m : ℕ) (beta : E) :
    (rightTailFreeShiftEquiv m beta).symm.toMonoidHom.comp
        (FreeGroup.map (insertedRightTailIndexToK m beta)) =
      FreeGroup.map (rightTailIndexToK m) := by
  refine FreeGroup.ext_hom _ _ fun l ↦ ?_
  simp only [MonoidHom.comp_apply, FreeGroup.map.of]
  apply (rightTailFreeShiftEquiv m beta).injective
  change (rightTailFreeShiftEquiv m beta)
      ((rightTailFreeShiftEquiv m beta).symm
        (FreeGroup.of (insertedRightTailIndexToK m beta l))) = _
  rw [MulEquiv.apply_symm_apply, rightTailFreeShiftEquiv_of]

/-- **Matched finite embedding identity.**  The source and target words indexed
by the common `RightTailIndex` are the same elements of the shared finite
cutter ambient.  Hence the finite cutter edge uses the identity isomorphism;
no global extension of insertion inside the cutter is required. -/
theorem rightTailMatched_restrict_eq (m : ℕ) (beta : E) :
    (rightTailMatchedTargetEmb m beta).comp
        (FreeGroup.map (insertedRightTailIndexToK m beta)) =
      (rightTailMatchedSourceEmb m).comp
        (FreeGroup.map (rightTailIndexToK m)) := by
  rw [rightTailMatchedTargetEmb, MonoidHom.comp_assoc,
    rightTailFreeShiftEquiv_symm_comp_inserted]

end Omega
end Higman
end GroupApproximation
