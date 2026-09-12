import GroupApproximation.CharClass.LemmaTwoBridge
import GroupApproximation.Analysis.LIXLemmaSixSouth

/-!
# The comparison algebra of Corollary 4

Corollary 4 says that a null-homotopy of the stage unitary would produce the
Murray--von Neumann equivalence Lemma 2 denies.  The production has two halves:
an analytic one, which glues the two hemisphere frames across the equator into
a continuous unitary field, and an algebraic one, which turns such a field into
the equivalence.  This file is the algebraic half, and it is short.

If `G` is a continuous field of unitaries of `M_{VIdx}` carrying `EHmat` to
`FHmat` by conjugation, then `w = G · EHmat` is a continuous field of partial
isometries with `wᴴ w = EHmat` and `w wᴴ = FHmat`, which is exactly
`ContinuousMvNEquiv EHmat FHmat`.  Nothing else about `G` is used, so this
lemma is the precise interface the analytic half has to hit: *a continuous
unitary field conjugating the constant complement onto the moving one*.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix
open CharClass

set_option linter.unusedSectionVars false

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- `EHmat` is a projection: block-diagonal with `𝟏³ − e₃ e₃ᴴ` and `H`. -/
theorem isStarProjection_EHmat (m : baseM dd) : IsStarProjection (EHmat m) := by
  rw [EHmat_eq_fromBlocks]
  exact STW59.isStarProjection_fromBlocks_diag
    (IsStarProjection.one_sub (STW59.isStarProjection_rankOneProj eThree_normSq))
    (isStarProjection_Hmat m)

theorem conjTranspose_EHmat (m : baseM dd) : (EHmat m)ᴴ = EHmat m :=
  STW59.conjTranspose_eq_of_isStarProjection (isStarProjection_EHmat m)

/-- **The comparison algebra.**  A continuous unitary field conjugating the
constant complement `EHmat` onto the moving one `FHmat` gives the
Murray--von Neumann equivalence of continuous fields.  This is the whole
algebraic content of Corollary 4; everything else in it is the construction of
`G`. -/
theorem continuousMvNEquiv_of_unitary_field
    {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ} (hG : Continuous G)
    (hu : ∀ m, (G m)ᴴ * G m = 1)
    (hconj : ∀ m, G m * EHmat m * (G m)ᴴ = FHmat m) :
    ContinuousMvNEquiv (EHmat (dd := dd)) (FHmat (dd := dd)) := by
  refine ⟨fun m => G m * EHmat m, hG.matrix_mul continuous_EHmat, fun m => ?_, fun m => ?_⟩
  · have hE := isStarProjection_EHmat m
    calc (G m * EHmat m)ᴴ * (G m * EHmat m)
        = EHmat m * ((G m)ᴴ * G m) * EHmat m := by
          rw [Matrix.conjTranspose_mul, conjTranspose_EHmat]
          simp only [Matrix.mul_assoc]
      _ = EHmat m := by rw [hu m, Matrix.mul_one, hE.isIdempotentElem.eq]
  · have hE := isStarProjection_EHmat m
    calc G m * EHmat m * (G m * EHmat m)ᴴ
        = G m * (EHmat m * EHmat m) * (G m)ᴴ := by
          rw [Matrix.conjTranspose_mul, conjTranspose_EHmat]
          simp only [Matrix.mul_assoc]
      _ = G m * EHmat m * (G m)ᴴ := by rw [hE.isIdempotentElem.eq]
      _ = FHmat m := hconj m

/-- The contrapositive, in the form `hstage` consumes: if Lemma 2 holds at
these dimensions then no such unitary field exists. -/
theorem not_exists_unitary_field
    (h : ¬ ContinuousMvNEquiv (EHmat (dd := dd)) (FHmat (dd := dd)))
    {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ} (hG : Continuous G)
    (hu : ∀ m, (G m)ᴴ * G m = 1)
    (hconj : ∀ m, G m * EHmat m * (G m)ᴴ = FHmat m) : False :=
  h (continuousMvNEquiv_of_unitary_field hG hu hconj)

end

end LIX
end GroupApproximation
