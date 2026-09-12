import GroupApproximation.CharClass.CohomologyKunnethStepOf
import GroupApproximation.CharClass.CohomologyKunnethSurjHelp
import GroupApproximation.CharClass.MayerVietorisZeroOf
import GroupApproximation.CharClass.CohomologyDeltaNaturalOf
import GroupApproximation.CharClass.CohomologyDeltaCupOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Künneth surjectivity with a sphere factor over a field: the Mayer–Vietoris steps

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethSurjHelp`, `CohomologyKunnethSurj` and
`CohomologyKunnethSurjStep` with coefficients in a field `K`.  A class on `Y × S^{n+1}` restricts
to the two hemispherical pieces; both restrictions come from one class `a` on `Y`, because they
agree on the band and the projection of the band is injective on cohomology.  So `z − pr^* a`
restricts to zero on both pieces and is in the image of the connecting map.  The band is `Y × S^n`,
the induction hypothesis decomposes the band class, and the two summands go through `δ` in opposite
ways: the pullback summand is killed, and δ-linearity turns the other into the suspended sphere
class cupped with a pullback.

**Signs.**  Over `F₂` the file adds `pr^* a` and cancels by `x + x = 0`.  Over `K` it subtracts:
`z − pr^* a` restricts to `pr^* a − pr^* a = 0`, and exactness at the ambient space
(`mvExactXOf`) needs no sign.  The honest restrictions `mvResWUOf`, `mvResWVOf` of lane `lix-lh`
make "the two restrictions agree on the band" an equation with no sign either.

## Main declarations

* `KnHemi.mvResUOf_pull_knPrY`, `KnHemi.mvResVOf_pull_knPrY`, `KnHemi.mvResWUOf_mvResUOf`,
  `KnHemi.mvResWVOf_mvResVOf`, `KnHemi.pull_prSub_band_injectiveOf`,
  `KnHemi.mvDeltaOf_pull_prSub_band`.
* `KnHemi.KnLowOf`, `KnHemi.KnTopOf` — the two halves of the decomposition.
* `KnHemi.exists_common_restrictionOf`, `KnHemi.exists_delta_of_subOf`,
  `KnHemi.knLow_zero_degreeOf`.
* `KnHemi.knLow_succOf`, `KnHemi.knTop_succOf` — the two induction steps.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-! ## 1. Restriction of a pullback from `Y` -/

theorem mvResUOf_pull_knPrY (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (a : Hmod K (TopCat.of Y) k) :
    (mvResUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom (pull (knPrY Y (n + 1)) k a)
      = pull (prSub Y n (hemiUSet Y n)) k a := by
  rw [mvResUOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, sInclusion_comp_prSub]

theorem mvResVOf_pull_knPrY (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (a : Hmod K (TopCat.of Y) k) :
    (mvResVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom (pull (knPrY Y (n + 1)) k a)
      = pull (prSub Y n (hemiVSet Y n)) k a := by
  rw [mvResVOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, sInclusion_comp_prSub]

/-! ## 2. The two restrictions to the band agree -/

theorem mvResWUOf_mvResUOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (z : Hmod K (prodTop Y n) k) :
    (mvResWUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
        ((mvResUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
      = pull (sInclusion (bandSet Y n)) k z := by
  rw [mvResWUOf_eq_pull, mvResUOf_eq_pull, cohPullbackK_apply_eq, cohPullbackK_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

theorem mvResWVOf_mvResVOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (z : Hmod K (prodTop Y n) k) :
    (mvResWVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
        ((mvResVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
      = pull (sInclusion (bandSet Y n)) k z := by
  rw [mvResWVOf_eq_pull, mvResVOf_eq_pull, cohPullbackK_apply_eq, cohPullbackK_apply_eq,
    ← pull_comp, subInclusion_comp_sInclusion]

/-! ## 3. The projection of the band is injective on cohomology -/

theorem pull_prSub_band_injectiveOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n k : ℕ) : Function.Injective (pull (K := K) (prSub Y n (bandSet Y n)) k) := by
  intro c₁ c₂ hc
  refine pull_knPrY_injectiveOf K Y n (spherePoint n) k ?_
  refine pull_bandHE_injectiveOf K Y n k ?_
  rw [pull_bandHE_knPrYOf, pull_bandHE_knPrYOf]
  exact hc

/-! ## 4. The connecting map kills a pullback from `Y` -/

theorem mvDeltaOf_pull_prSub_band (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    (n k : ℕ) (c : Hmod K (TopCat.of Y) k) :
    (mvDeltaOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom
      (pull (prSub Y n (bandSet Y n)) k c) = 0 := by
  refine (mvExactWOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k _).2 ?_
  refine ⟨pull (prSub Y n (hemiUSet Y n)) k c, 0, ?_⟩
  rw [mvResWUOf_pull_prSub, map_zero, add_zero]

/-! ## 5. The two halves of the decomposition -/

/-- Below the sphere dimension every class is pulled back from the base, over `K`. -/
def KnLowOf (K : Type) [CommRing K] (n : ℕ) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (k : ℕ), k < n →
    ∀ z : Hmod K (TopCat.of (Y × Sphere n)) k,
      ∃ a : Hmod K (TopCat.of Y) k, z = pull (knPrY Y n) k a

/-- In degree `n + m` every class splits into a pullback and a multiple of the sphere class,
over `K`.  The degree is carried as an explicit equation, as in `KnTop`. -/
def KnTopOf (K : Type) [CommRing K] (n : ℕ) (t : Hmod K (TopCat.of (Sphere n)) n) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (k m : ℕ) (hk : n + m = k)
    (z : Hmod K (TopCat.of (Y × Sphere n)) k),
    ∃ (a : Hmod K (TopCat.of Y) k) (b : Hmod K (TopCat.of Y) m),
      z = pull (knPrY Y n) k a
        + cohCast hk (cup (pull (knPrS Y n) n t) (pull (knPrY Y n) m b))

/-! ## 6. The two restrictions come from one class on the base -/

set_option maxHeartbeats 1000000 in
theorem exists_common_restrictionOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    (n k : ℕ) (z : Hmod K (prodTop Y n) k) :
    ∃ a : Hmod K (TopCat.of Y) k,
      (mvResUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z
          = pull (prSub Y n (hemiUSet Y n)) k a
        ∧ (mvResVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z
          = pull (prSub Y n (hemiVSet Y n)) k a := by
  obtain ⟨aU, haU⟩ := exists_pull_prSub_hemiUOf K Y n k
    ((mvResUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
  obtain ⟨aV, haV⟩ := exists_pull_prSub_hemiVOf K Y n k
    ((mvResVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
  have hband : pull (prSub Y n (bandSet Y n)) k aU
      = pull (prSub Y n (bandSet Y n)) k aV := by
    rw [← mvResWUOf_pull_prSub, ← mvResWVOf_pull_prSub, haU, haV, mvResWUOf_mvResUOf,
      mvResWVOf_mvResVOf]
  have hEq : aU = aV := pull_prSub_band_injectiveOf K Y n k hband
  refine ⟨aU, haU.symm, ?_⟩
  rw [hEq]
  exact haV.symm

/-! ## 7. Every class is a pullback plus a connecting-map image -/

set_option maxHeartbeats 1000000 in
theorem exists_delta_of_subOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n j : ℕ)
    (z : Hmod K (prodTop Y n) (j + 1)) :
    ∃ (a : Hmod K (TopCat.of Y) (j + 1)) (w : Hmod K (TopCat.of ↥(bandSet Y n)) j),
      z = pull (knPrY Y (n + 1)) (j + 1) a
        + (mvDeltaOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j).hom w := by
  obtain ⟨a, hU, hV⟩ := exists_common_restrictionOf K Y n (j + 1) z
  have hU' : (mvResUOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (j + 1)).hom
      (z - pull (knPrY Y (n + 1)) (j + 1) a) = 0 := by
    rw [map_sub, mvResUOf_pull_knPrY, hU, sub_self]
  have hV' : (mvResVOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (j + 1)).hom
      (z - pull (knPrY Y (n + 1)) (j + 1) a) = 0 := by
    rw [map_sub, mvResVOf_pull_knPrY, hV, sub_self]
  obtain ⟨w, hw⟩ := (mvExactXOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j
    (z - pull (knPrY Y (n + 1)) (j + 1) a)).1 ⟨hU', hV'⟩
  refine ⟨a, w, ?_⟩
  rw [hw, add_sub_cancel]

/-! ## 8. Degree zero -/

theorem knLow_zero_degreeOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (z : Hmod K (prodTop Y n) 0) :
    ∃ a : Hmod K (TopCat.of Y) 0, z = pull (knPrY Y (n + 1)) 0 a := by
  obtain ⟨a, hU, hV⟩ := exists_common_restrictionOf K Y n 0 z
  refine ⟨a, ?_⟩
  have h0 : z - pull (knPrY Y (n + 1)) 0 a = 0 := by
    refine mvExactZeroOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) ?_ ?_
    · rw [map_sub, mvResUOf_pull_knPrY, hU, sub_self]
    · rw [map_sub, mvResVOf_pull_knPrY, hV, sub_self]
  exact sub_eq_zero.1 h0

/-! ## 9. The induction steps -/

/-- **The connecting map sends the band class to the suspended sphere class**, over `K`. -/
theorem mvDeltaOf_bandRestrict (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (t₀ : Hmod K (TopCat.of (Sphere n)) n) :
    (mvDeltaOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) n).hom
        (pull (bandRestrict Y n) n (pull (cmap (bandToSphere n)) n t₀))
      = pull (knPrS Y (n + 1)) (n + 1) (sphereNextOf K n t₀) :=
  MVDelta.mvDeltaOf_naturality K (knPrS Y (n + 1)) (upperOpens n) (lowerOpens n)
    (upperOpens_sup_lowerOpens n) n (pull (cmap (bandToSphere n)) n t₀)

/-- Every class on the band is transported from `Y × S^n`, over `K`. -/
theorem exists_band_transportOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (n j : ℕ) (w : Hmod K (TopCat.of ↥(bandSet Y n)) j) :
    ∃ w' : Hmod K (TopCat.of (Y × Sphere n)) j,
      pull (cmap (bandHomotopyEquiv Y n).toFun) j w' = w :=
  ⟨(bandPullEquivOf K Y n j).symm w, (bandPullEquivOf K Y n j).apply_symm_apply w⟩

set_option maxHeartbeats 1000000 in
/-- **The low step over `K`.** -/
theorem knLow_succOf (K : Type) [Field K] (n : ℕ) (hlow : KnLowOf K n) : KnLowOf K (n + 1) := by
  intro Y _ k hk z
  match k with
  | 0 => exact knLow_zero_degreeOf K Y n z
  | (j + 1) =>
    obtain ⟨a, w, hz⟩ := exists_delta_of_subOf K Y n j z
    obtain ⟨w', hw'⟩ := exists_band_transportOf K Y n j w
    obtain ⟨c, hc⟩ := hlow Y j (by omega) w'
    refine ⟨a, ?_⟩
    rw [hz, ← hw', hc, pull_bandHE_knPrYOf, mvDeltaOf_pull_prSub_band, add_zero]

set_option maxHeartbeats 1000000 in
/-- **The top step over `K`.** -/
theorem knTop_succOf (K : Type) [Field K] (n : ℕ) (t₀ : Hmod K (TopCat.of (Sphere n)) n)
    (htop : KnTopOf K n t₀) : KnTopOf K (n + 1) (sphereNextOf K n t₀) := by
  intro Y _ k m hk z
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨n + m, by omega⟩
  obtain ⟨a, w, hz⟩ := exists_delta_of_subOf K Y n j z
  obtain ⟨w', hw'⟩ := exists_band_transportOf K Y n j w
  obtain ⟨c, d, hcd⟩ := htop Y j m (by omega) w'
  refine ⟨a, d, ?_⟩
  -- the pullback summand of the band class is killed by `δ`
  have hband : (mvDeltaOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j).hom w
      = (mvDeltaOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j).hom
          (pull (cmap (bandHomotopyEquiv Y n).toFun) j
            (cohCast (show n + m = j by omega)
              (cup (pull (knPrS Y n) n t₀) (pull (knPrY Y n) m d)))) := by
    rw [← hw', hcd, pull_add, pull_bandHE_knPrYOf, map_add, mvDeltaOf_pull_prSub_band,
      zero_add]
  rw [hz, hband]
  congr 1
  -- what is left is δ-linearity
  obtain rfl : j = n + m := by omega
  rw [CharClass.cohCast_self, pull_cup, pull_bandHE_knPrSOf, pull_bandHE_knPrYOf,
    ← pull_sInclusion_knPrYOf, MVDelta.mvDeltaOf_cup, mvDeltaOf_bandRestrict]

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.exists_delta_of_subOf
#audit_axioms KnHemi.knLow_succOf
#audit_axioms KnHemi.knTop_succOf

end GroupApproximation.CharClass
