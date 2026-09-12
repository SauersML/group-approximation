import GroupApproximation.CharClass.CohomologyDeltaCupOf

/-!
# Naturality of the Mayer–Vietoris connecting map over a field

The coefficient-generic form of `CohomologyDeltaNatural`.  Take cochain data for `w` on `X`
(`mvDeltaOf_data`), pull every piece of it back along `f`, check the three conditions using
contravariant functoriality of `cochainPullback` and the three commuting squares of spaces
of `MayerVietorisNaturality`, and read off both sides with `mvDeltaOf_spec`.  The difference
condition `α_U| − α_V| = α` survives pullback because pullback is additive.

## Main result

* `MVDelta.mvDeltaOf_naturality` — `δ_Z ∘ (interRestrict f)^* = f^* ∘ δ_X`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X Z : TopCat.{0}}

/-- **Naturality of the Mayer–Vietoris connecting map over a field.** -/
theorem mvDeltaOf_naturality (K : Type) [Field K] (f : Z ⟶ X) (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (w : Hmod K (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n) :
    (mvDeltaOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull (interRestrict f U V) n w)
      = pull f (n + 1) ((mvDeltaOf K U V hUV n).hom w) := by
  obtain ⟨α, hα, aU, aV, γ, hγ, hacls, haUV, hγU, hγV⟩ := mvDeltaOf_data K U V hUV n w
  -- the value of `δ` on `w`
  have hdelta : (mvDeltaOf K U V hUV n).hom w = cocycleClassK K X (n + 1) γ hγ := by
    rw [← hacls]
    exact mvDeltaOf_spec K U V hUV n α hα aU aV haUV γ hγ hγU hγV
  -- the transported cochains are cocycles
  have hαZ : cochainCoboundary K
      (TopCat.of ↥(((opensComap f U : Opens Z) : Set Z)
        ∩ ((opensComap f V : Opens Z) : Set Z))) n
      (cochainPullback (interRestrict f U V) n α) = 0 := by
    rw [← cochainPullback_coboundaryOf, hα, cochainPullback_zeroOf]
  have hγZ : cochainCoboundary K Z (n + 1) (cochainPullback f (n + 1) γ) = 0 := by
    rw [← cochainPullback_coboundaryOf, hγ, cochainPullback_zeroOf]
  -- the two pieces still differ by `α`
  have haUVZ : cochainPullback (subInclusion Set.inter_subset_left) n
        (cochainPullback (opensRestrict f U) n aU)
      - cochainPullback (subInclusion Set.inter_subset_right) n
        (cochainPullback (opensRestrict f V) n aV)
      = cochainPullback (interRestrict f U V) n α := by
    rw [← cochainPullback_compK, ← cochainPullback_compK,
      ← interRestrict_comp_subInclusionLeft, ← interRestrict_comp_subInclusionRight,
      cochainPullback_compK, cochainPullback_compK, ← cochainPullback_subOf, haUV]
  -- the ambient cochain still restricts to the two coboundaries
  have hγUZ : cochainPullback (sInclusion ((opensComap f U : Opens Z) : Set Z)) (n + 1)
        (cochainPullback f (n + 1) γ)
      = cochainCoboundary K (TopCat.of ((opensComap f U : Opens Z) : Set Z)) n
          (cochainPullback (opensRestrict f U) n aU) := by
    rw [← cochainPullback_compK, ← opensRestrict_comp_sInclusion,
      cochainPullback_compK, hγU, cochainPullback_coboundaryOf]
  have hγVZ : cochainPullback (sInclusion ((opensComap f V : Opens Z) : Set Z)) (n + 1)
        (cochainPullback f (n + 1) γ)
      = cochainCoboundary K (TopCat.of ((opensComap f V : Opens Z) : Set Z)) n
          (cochainPullback (opensRestrict f V) n aV) := by
    rw [← cochainPullback_compK, ← opensRestrict_comp_sInclusion,
      cochainPullback_compK, hγV, cochainPullback_coboundaryOf]
  -- read both sides off
  rw [hdelta, pull_mkOf, ← hacls, pull_mkOf,
    mvDeltaOf_spec K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n
      (cochainPullback (interRestrict f U V) n α) hαZ
      (cochainPullback (opensRestrict f U) n aU)
      (cochainPullback (opensRestrict f V) n aV) haUVZ
      (cochainPullback f (n + 1) γ) hγZ hγUZ hγVZ]

end MVDelta

end

end GroupApproximation.CharClass
