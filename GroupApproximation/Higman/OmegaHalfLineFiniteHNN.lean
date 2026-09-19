import GroupApproximation.Higman.OmegaHalfLineMatchedFiniteCutter

/-!
# The actual finite HNN edge for right insertion

The matched construction has one finitely presented torsion-free ambient and
one finitely generated cutter.  Its central HNN extension is therefore again
finitely presented and torsion-free.  Although the two label embeddings are
different globally, their restrictions to the common right-tail basis agree;
the stable letter consequently carries every source basis word to its named
inserted target word.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-- The common finite cutting subgroup. -/
noncomputable abbrev rightTailMatchedCutter (m : ℕ) :
    Subgroup (rightTailMatchedAmbient m) :=
  (rightTailPairedEqualizerWitness m).witness.L

/-- The finite HNN extension realizing the matched right-insertion edge. -/
noncomputable abbrev RightTailMatchedExtension (m : ℕ) : Type :=
  CentHNN (rightTailMatchedCutter m)

theorem rightTailIndexToK_range (m : ℕ) :
    Set.range (rightTailIndexToK m) = rightTailLabel m := by
  ext q
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨(l : E), l.property, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

/-- Every common source-basis word lands in the finite cutter. -/
theorem rightTailMatchedSource_word_mem_cutter
    (m : ℕ) (w : FreeGroup (RightTailIndex m)) :
    rightTailMatchedSourceEmb m
        (FreeGroup.map (rightTailIndexToK m) w) ∈
      rightTailMatchedCutter m := by
  rw [← Subgroup.mem_comap,
    rightTailMatchedCutter_comap_source]
  have hw := CentralHNNFreeLabel.Coordinate.map_mem_closure_range
    (rightTailIndexToK m) w
  rwa [rightTailIndexToK_range] at hw

/-- **Finite HNN insertion relation.**  Conjugation by the stable letter
carries source evaluation of every abstract right-tail word to target
evaluation of the same word with all labels inserted by `beta`. -/
theorem rightTailMatched_stable_conj
    (m : ℕ) (beta : E) (w : FreeGroup (RightTailIndex m)) :
    (t : RightTailMatchedExtension m)⁻¹ *
        of (rightTailMatchedSourceEmb m
          (FreeGroup.map (rightTailIndexToK m) w)) * t =
      of (rightTailMatchedTargetEmb m beta
        (FreeGroup.map (insertedRightTailIndexToK m beta) w)) := by
  rw [conj_eq_self_of_mem (rightTailMatchedCutter m)
    (rightTailMatchedSource_word_mem_cutter m w)]
  exact congrArg of
    (DFunLike.congr_fun (rightTailMatched_restrict_eq m beta) w).symm

/-- Finite presentability is now literal: the ambient is finitely presented
and the associated subgroup is the finitely generated matched cutter. -/
theorem rightTailMatchedExtension_finitelyPresented (m : ℕ) :
    Group.IsFinitelyPresented (RightTailMatchedExtension m) :=
  isFinitelyPresented_centHNN (rightTailMatchedCutter m)
    (rightTailPairedEqualizerWitness m).witness.L_fg

/-- Torsion-freeness survives the central HNN extension. -/
theorem rightTailMatchedExtension_torsionFree (m : ℕ) :
    IsPowerTorsionFree (RightTailMatchedExtension m) :=
  HNNBritton.isPowerTorsionFree_hnn
    (MulEquiv.refl (rightTailMatchedCutter m))
    (rightTailPairedEqualizerWitness m).torsionFree

end Omega
end Higman
end GroupApproximation
