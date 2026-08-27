import GroupApproximation.Matching.AsymptoticPartialBijection
import GroupApproximation.Matching.FiniteGroupoidPresentation

/-!
# The asymptotic partial-bijection groupoid

For any family of finite models over a common nonnegative scale, sequences of
co-negligible partial bijections form a genuine groupoid after quotienting by
negligible two-sided disagreement.  All representative laws and all quotient
compatibility statements are proved in the imported finite/asymptotic layers.
-/

namespace GroupApproximation

/-- The concrete groupoid presentation carried by asymptotic partial
bijections between a family of finite-model sequences. -/
noncomputable def asymptoticPartialGroupoidPresentation
    (I : Type*) (N : ℕ → ℝ) (hN : ∀ n, 0 ≤ N n)
    (model : I → ℕ → FiniteModel) : GroupoidPresentation I where
  Rep X Y := AsymptoticPartialBijection N (model X) (model Y)
  rel X Y := AsymptoticPartialBijection.nearSetoid hN
  one X := AsymptoticPartialBijection.refl N (model X)
  comp f g := f.trans hN g
  inv f := f.symm
  comp_respects hf hg :=
    AsymptoticPartialBijection.trans_near_congr hN hf hg
  inv_respects hf := AsymptoticPartialBijection.symm_near_congr hf
  one_comp f := by
    change AsymptoticPartialBijection.Near
      ((AsymptoticPartialBijection.refl N _).trans hN f) f
    rw [AsymptoticPartialBijection.refl_trans]
    exact AsymptoticPartialBijection.near_refl f
  comp_one f := by
    change AsymptoticPartialBijection.Near
      (f.trans hN (AsymptoticPartialBijection.refl N _)) f
    rw [AsymptoticPartialBijection.trans_refl]
    exact AsymptoticPartialBijection.near_refl f
  assoc f g h := by
    change AsymptoticPartialBijection.Near
      ((f.trans hN g).trans hN h) (f.trans hN (g.trans hN h))
    rw [AsymptoticPartialBijection.trans_assoc]
    exact AsymptoticPartialBijection.near_refl _
  inv_comp f := by
    change AsymptoticPartialBijection.Near (f.symm.trans hN f)
      (AsymptoticPartialBijection.refl N _)
    rw [AsymptoticPartialBijection.symm_trans_self]
    exact AsymptoticPartialBijection.reflOn_near_refl _ f.target_negligible
  comp_inv f := by
    change AsymptoticPartialBijection.Near (f.trans hN f.symm)
      (AsymptoticPartialBijection.refl N _)
    rw [AsymptoticPartialBijection.trans_symm]
    exact AsymptoticPartialBijection.reflOn_near_refl _ f.source_negligible

end GroupApproximation
