import GroupApproximation.CharClass.CohomologyKunnethSurj

/-!
# The induction for Künneth surjectivity

`exists_delta_of_sub` writes a class on `Y × S^{n+1}` as a pullback from `Y` plus
the connecting-map image of a class on the band.  The band is `Y × S^n`, so the
induction hypothesis decomposes that class, and the two summands go through `δ`
in opposite ways: the pullback summand is killed, and δ-linearity turns the other
into the sphere class of the bigger sphere cupped with a pullback.

## Main declarations

* `KnHemi.mvDelta_bandRestrict` — `δ` of the band class is the suspended class.
* `KnHemi.knLow_succ`, `KnHemi.knTop_succ` — the two induction steps.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-- **The connecting map sends the band class to the suspended sphere class.**  This
is `mvDelta_naturality` along the sphere projection; the preimage cover of the
hemispheres is the product cover on the nose. -/
theorem mvDelta_bandRestrict (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (t₀ : Hmod2 (TopCat.of (Sphere n)) n) :
    (mvDelta (hemiU Y n) (hemiV Y n) (hemi_sup Y n) n).hom
        (pull (bandRestrict Y n) n (pull (cmap (bandToSphere n)) n t₀))
      = pull (knPrS Y (n + 1)) (n + 1) (sphereNext n t₀) :=
  MVDelta.mvDelta_naturality (knPrS Y (n + 1)) (upperOpens n) (lowerOpens n)
    (upperOpens_sup_lowerOpens n) n (pull (cmap (bandToSphere n)) n t₀)

/-- Every class on the band is transported from `Y × S^n`. -/
theorem exists_band_transport (Y : Type) [TopologicalSpace Y] (n j : ℕ)
    (w : Hmod2 (TopCat.of ↥(bandSet Y n)) j) :
    ∃ w' : Hmod2 (TopCat.of (Y × Sphere n)) j,
      pull (cmap (bandHomotopyEquiv Y n).toFun) j w' = w :=
  ⟨(bandPullEquiv Y n j).symm w, (bandPullEquiv Y n j).apply_symm_apply w⟩

/-! ## The low step -/

set_option maxHeartbeats 1000000 in
theorem knLow_succ (n : ℕ) (hlow : KnLow n) : KnLow (n + 1) := by
  intro Y _ k hk z
  match k with
  | 0 => exact knLow_zero_degree Y n z
  | (j + 1) =>
    obtain ⟨a, w, hz⟩ := exists_delta_of_sub Y n j z
    obtain ⟨w', hw'⟩ := exists_band_transport Y n j w
    obtain ⟨c, hc⟩ := hlow Y j (by omega) w'
    refine ⟨a, ?_⟩
    rw [hz, ← hw', hc, pull_bandHE_knPrY, mvDelta_pull_prSub_band, add_zero]

/-! ## The top step -/

set_option maxHeartbeats 1000000 in
theorem knTop_succ (n : ℕ) (t₀ : Hmod2 (TopCat.of (Sphere n)) n)
    (htop : KnTop n t₀) : KnTop (n + 1) (sphereNext n t₀) := by
  intro Y _ k m hk z
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨n + m, by omega⟩
  obtain ⟨a, w, hz⟩ := exists_delta_of_sub Y n j z
  obtain ⟨w', hw'⟩ := exists_band_transport Y n j w
  obtain ⟨c, d, hcd⟩ := htop Y j m (by omega) w'
  refine ⟨a, d, ?_⟩
  -- the pullback summand of the band class is killed by `δ`
  have hband : (mvDelta (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j).hom w
      = (mvDelta (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j).hom
          (pull (cmap (bandHomotopyEquiv Y n).toFun) j
            (cohCast (show n + m = j by omega)
              (cup (pull (knPrS Y n) n t₀) (pull (knPrY Y n) m d)))) := by
    rw [← hw', hcd, pull_add, pull_bandHE_knPrY, map_add, mvDelta_pull_prSub_band,
      zero_add]
  rw [hz, hband]
  congr 1
  -- what is left is δ-linearity
  obtain rfl : j = n + m := by omega
  rw [pull_cohCast, cohCast_rfl, pull_cup, pull_bandHE_knPrS, pull_bandHE_knPrY,
    ← pull_sInclusion_knPrY, MVDelta.mvDelta_cup, mvDelta_bandRestrict]

end KnHemi

end

end GroupApproximation.CharClass
