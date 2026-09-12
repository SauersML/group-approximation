import GroupApproximation.CharClass.CohomologyDeltaCup
import GroupApproximation.CharClass.MayerVietorisNaturality

/-!
# Naturality of the Mayer–Vietoris connecting map

`MayerVietorisNaturality.lean` proves the four restriction squares for a map
`f : Z ⟶ X` of covered spaces and records that the fifth, for the connecting map,
needs a cochain-level description of `δ`.  That description is `mvDelta_spec`, so
the square is proved here.

The argument is the only one available: take cochain data for `w` on `X`
(`mvDelta_data`), pull every piece of it back along `f`, check the three
conditions using contravariant functoriality of `cochainPullback` and the three
commuting squares of *spaces* that `cc-thom` proved by `rfl`, and read off both
sides with `mvDelta_spec`.

## Main result

* `MVDelta.mvDelta_naturality` — `δ_Z ∘ (interRestrict f)^* = f^* ∘ δ_X`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace MVDelta

variable {X Z : TopCat.{0}}

theorem cochainPullback_add (f : Z ⟶ X) (n : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X n) :
    cochainPullback f n (φ + ψ) = cochainPullback f n φ + cochainPullback f n ψ :=
  map_add _ _ _

/-- **Naturality of the Mayer–Vietoris connecting map.**  For `f : Z ⟶ X` and a
two-element open cover of `X`, the connecting map of the preimage cover applied to
the restriction of `w` is the restriction of the connecting map applied to `w`. -/
theorem mvDelta_naturality (f : Z ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (w : Hmod2 (TopCat.of ↥((U : Set X) ∩ (V : Set X))) n) :
    (mvDelta (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n).hom
        (pull (interRestrict f U V) n w)
      = pull f (n + 1) ((mvDelta U V hUV n).hom w) := by
  obtain ⟨α, hα, aU, aV, γ, hγ, hacls, haUV, hγU, hγV⟩ := mvDelta_data U V hUV n w
  -- the value of `δ` on `w`
  have hdelta : (mvDelta U V hUV n).hom w = cocycleClass X (n + 1) γ hγ := by
    rw [← hacls]
    exact mvDelta_spec U V hUV n α hα aU aV haUV γ hγ hγU hγV
  -- the transported cochains are cocycles
  have hαZ : cochainCoboundary (ZMod 2)
      (TopCat.of ↥(((opensComap f U : Opens Z) : Set Z)
        ∩ ((opensComap f V : Opens Z) : Set Z))) n
      (cochainPullback (interRestrict f U V) n α) = 0 := by
    rw [← cochainPullback_coboundary', hα, cochainPullback_zero]
  have hγZ : cochainCoboundary (ZMod 2) Z (n + 1)
      (cochainPullback f (n + 1) γ) = 0 := by
    rw [← cochainPullback_coboundary', hγ, cochainPullback_zero]
  -- the two pieces still add up to `α`
  have haUVZ : cochainPullback (subInclusion Set.inter_subset_left) n
        (cochainPullback (opensRestrict f U) n aU)
      + cochainPullback (subInclusion Set.inter_subset_right) n
        (cochainPullback (opensRestrict f V) n aV)
      = cochainPullback (interRestrict f U V) n α := by
    rw [← cochainPullback_comp', ← cochainPullback_comp',
      ← interRestrict_comp_subInclusionLeft, ← interRestrict_comp_subInclusionRight,
      cochainPullback_comp', cochainPullback_comp', ← cochainPullback_add, haUV]
  -- the ambient cochain still restricts to the two coboundaries
  have hγUZ : cochainPullback (sInclusion ((opensComap f U : Opens Z) : Set Z)) (n + 1)
        (cochainPullback f (n + 1) γ)
      = cochainCoboundary (ZMod 2)
          (TopCat.of ((opensComap f U : Opens Z) : Set Z)) n
          (cochainPullback (opensRestrict f U) n aU) := by
    rw [← cochainPullback_comp', ← opensRestrict_comp_sInclusion,
      cochainPullback_comp', hγU, cochainPullback_coboundary']
  have hγVZ : cochainPullback (sInclusion ((opensComap f V : Opens Z) : Set Z)) (n + 1)
        (cochainPullback f (n + 1) γ)
      = cochainCoboundary (ZMod 2)
          (TopCat.of ((opensComap f V : Opens Z) : Set Z)) n
          (cochainPullback (opensRestrict f V) n aV) := by
    rw [← cochainPullback_comp', ← opensRestrict_comp_sInclusion,
      cochainPullback_comp', hγV, cochainPullback_coboundary']
  -- read both sides off
  rw [hdelta, pull_mk, ← hacls, pull_mk,
    mvDelta_spec (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV) n
      (cochainPullback (interRestrict f U V) n α) hαZ
      (cochainPullback (opensRestrict f U) n aU)
      (cochainPullback (opensRestrict f V) n aV) haUVZ
      (cochainPullback f (n + 1) γ) hγZ hγUZ hγVZ]

end MVDelta

end

end GroupApproximation.CharClass
