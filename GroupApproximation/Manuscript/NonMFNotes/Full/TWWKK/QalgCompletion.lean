import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgNorm

/-!
# The full unital C⋆-free product `A * A`

`FreeUnital A` is the completion of the normed `⋆`-algebra `PreFree A` (`QalgNorm`) for the
universal C⋆-norm.  The involution extends by uniform continuity, and the C⋆-identity, the
`⋆`-ring laws and the `⋆`-module law pass to the completion by density, so `FreeUnital A` is a
unital C⋆-algebra in the universe of `A`.

This is the unital full free product `A * A` in Cuntz's construction of `qA`
(J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(Tikuisis--White--Winter), lane TWWKK-Qalg, work order WO-TWWKK-A2.
-/

namespace GroupApproximation.Full.TWWKK

namespace FreeProd

open UniformSpace

universe u

noncomputable section

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The full unital C⋆-free product `A * A`: the completion of `PreFree A`. -/
abbrev FreeUnital (A : Type u) [NonUnitalCStarAlgebra A] : Type u :=
  Completion (PreFree A)

theorem uniformContinuous_star_pre : UniformContinuous (star : PreFree A → PreFree A) :=
  AddMonoidHomClass.uniformContinuous_of_bound (starAddEquiv : PreFree A ≃+ PreFree A) 1
    fun x => by
      rw [one_mul]
      exact (norm_star x).le

instance instStarFree : Star (FreeUnital A) where
  star := Completion.map (star : PreFree A → PreFree A)

theorem star_coe (x : PreFree A) :
    star (x : Completion (PreFree A)) = ((star x : PreFree A) : Completion (PreFree A)) :=
  Completion.map_coe uniformContinuous_star_pre x

instance instContinuousStarFree : ContinuousStar (FreeUnital A) :=
  ⟨Completion.continuous_map⟩

instance instStarRingFree : StarRing (FreeUnital A) where
  star_involutive x := by
    refine Completion.induction_on x
      (isClosed_eq (continuous_star.comp continuous_star) continuous_id) ?_
    intro a
    rw [star_coe, star_coe, star_star]
  star_mul x y := by
    refine Completion.induction_on₂ x y
      (isClosed_eq (continuous_star.comp continuous_mul)
        ((continuous_star.comp continuous_snd).mul (continuous_star.comp continuous_fst))) ?_
    intro a b
    rw [← Completion.coe_mul, star_coe, star_coe, star_coe, ← Completion.coe_mul, star_mul]
  star_add x y := by
    refine Completion.induction_on₂ x y
      (isClosed_eq (continuous_star.comp continuous_add)
        ((continuous_star.comp continuous_fst).add (continuous_star.comp continuous_snd))) ?_
    intro a b
    rw [← Completion.coe_add, star_coe, star_coe, star_coe, ← Completion.coe_add, star_add]

instance instStarModuleFree : StarModule ℂ (FreeUnital A) where
  star_smul c x := by
    refine Completion.induction_on x
      (isClosed_eq (continuous_star.comp (continuous_const_smul c))
        ((continuous_const_smul (star c)).comp continuous_star)) ?_
    intro a
    rw [← Completion.coe_smul, star_coe, star_coe, ← Completion.coe_smul, star_smul]

instance instCStarRingFree : CStarRing (FreeUnital A) where
  norm_mul_self_le x := by
    refine Completion.induction_on x
      (isClosed_le (continuous_norm.mul continuous_norm)
        (continuous_norm.comp (continuous_star.mul continuous_id))) ?_
    intro a
    rw [star_coe, ← Completion.coe_mul, Completion.norm_coe, Completion.norm_coe]
    exact CStarRing.norm_mul_self_le a

instance instNormedAlgebraFree : NormedAlgebra ℂ (FreeUnital A) where
  norm_smul_le := norm_smul_le

/-- The full unital free product `A * A` is a unital C⋆-algebra. -/
instance instCStarAlgebraFree : CStarAlgebra (FreeUnital A) where

end

end FreeProd

end GroupApproximation.Full.TWWKK
