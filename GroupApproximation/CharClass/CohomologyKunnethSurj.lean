import GroupApproximation.CharClass.CohomologyKunnethSurjHelp

/-!
# Künneth surjectivity: the two Mayer–Vietoris steps

The decomposition of a class on `Y × S^{n+1}` starts by removing its pullback
part.  Restricting to the two hemispherical pieces gives two classes on `Y`; they
agree, because both restrict to the same class on the band and the projection of
the band is injective on cohomology.  Subtracting the common class leaves a class
restricting to zero on both pieces, which is therefore in the image of the
connecting map.

That is `exists_delta_of_sub`, and the induction on the sphere dimension is then
a matter of decomposing the band class and pushing the two summands through `δ`:
the pullback summand dies, and δ-linearity turns the other into the sphere class
of the bigger sphere cupped with a pullback.

## Main declarations

* `KnHemi.KnLow`, `KnHemi.KnTop` — the two halves of the decomposition.
* `KnHemi.exists_common_restriction` — the two restrictions come from one class.
* `KnHemi.exists_delta_of_sub` — every class is a pullback plus a `δ`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

/-! ## 1. The two halves of the decomposition -/

/-- Below the sphere dimension every class is pulled back from the base. -/
def KnLow (n : ℕ) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (k : ℕ), k < n →
    ∀ z : Hmod2 (TopCat.of (Y × Sphere n)) k,
      ∃ a : Hmod2 (TopCat.of Y) k, z = pull (knPrY Y n) k a

/-- In degree `n + m` every class splits into a pullback and a multiple of the
sphere class.  The degree is carried as an explicit equation rather than as
`n + m`, so that the induction step never has to transport `z` itself: at `n + 1`
the degree is `(n + m) + 1`, which is not `(n + 1) + m` on the nose. -/
def KnTop (n : ℕ) (t : Hmod2 (TopCat.of (Sphere n)) n) : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] (k m : ℕ) (hk : n + m = k)
    (z : Hmod2 (TopCat.of (Y × Sphere n)) k),
    ∃ (a : Hmod2 (TopCat.of Y) k) (b : Hmod2 (TopCat.of Y) m),
      z = pull (knPrY Y n) k a
        + cohCast hk (cup (pull (knPrS Y n) n t) (pull (knPrY Y n) m b))

theorem pull_cohCast {X Z : TopCat.{0}} (f : X ⟶ Z) {m m' : ℕ} (h : m = m')
    (a : Hmod2 Z m) : pull f m' (cohCast h a) = cohCast h (pull f m a) := by
  subst h
  rfl

/-! ## 2. The two restrictions come from one class on the base -/

set_option maxHeartbeats 1000000 in
theorem exists_common_restriction (Y : Type) [TopologicalSpace Y] (n k : ℕ)
    (z : Hmod2 (prodTop Y n) k) :
    ∃ a : Hmod2 (TopCat.of Y) k,
      (mvResU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z
          = pull (prSub Y n (hemiUSet Y n)) k a
        ∧ (mvResV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z
          = pull (prSub Y n (hemiVSet Y n)) k a := by
  obtain ⟨aU, haU⟩ := exists_pull_prSub_hemiU Y n k
    ((mvResU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
  obtain ⟨aV, haV⟩ := exists_pull_prSub_hemiV Y n k
    ((mvResV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) k).hom z)
  have hband : pull (prSub Y n (bandSet Y n)) k aU
      = pull (prSub Y n (bandSet Y n)) k aV := by
    rw [← mvResWU_pull_prSub, ← mvResWV_pull_prSub, haU, haV, mvResWU_mvResU,
      mvResWV_mvResV]
  have hEq : aU = aV := pull_prSub_band_injective Y n k hband
  refine ⟨aU, haU.symm, ?_⟩
  rw [hEq]
  exact haV.symm

/-! ## 3. Every class is a pullback plus a connecting-map image -/

set_option maxHeartbeats 1000000 in
theorem exists_delta_of_sub (Y : Type) [TopologicalSpace Y] (n j : ℕ)
    (z : Hmod2 (prodTop Y n) (j + 1)) :
    ∃ (a : Hmod2 (TopCat.of Y) (j + 1))
      (w : Hmod2 (TopCat.of ↥(bandSet Y n)) j),
      z = pull (knPrY Y (n + 1)) (j + 1) a
        + (mvDelta (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j).hom w := by
  obtain ⟨a, hU, hV⟩ := exists_common_restriction Y n (j + 1) z
  have hU' : (mvResU (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (j + 1)).hom
      (z + pull (knPrY Y (n + 1)) (j + 1) a) = 0 := by
    rw [map_add, mvResU_pull_knPrY, hU, add_self_eq_zero_two _]
  have hV' : (mvResV (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (j + 1)).hom
      (z + pull (knPrY Y (n + 1)) (j + 1) a) = 0 := by
    rw [map_add, mvResV_pull_knPrY, hV, add_self_eq_zero_two _]
  obtain ⟨w, hw⟩ := (mvExactX (hemiU Y n) (hemiV Y n) (hemi_sup Y n) j
    (z + pull (knPrY Y (n + 1)) (j + 1) a)).1 ⟨hU', hV'⟩
  refine ⟨a, w, ?_⟩
  rw [hw, add_comm z, ← add_assoc, add_self_eq_zero_two _, zero_add]

/-! ## 4. Below the sphere dimension in degree zero -/

theorem knLow_zero_degree (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (z : Hmod2 (prodTop Y n) 0) :
    ∃ a : Hmod2 (TopCat.of Y) 0, z = pull (knPrY Y (n + 1)) 0 a := by
  obtain ⟨a, hU, hV⟩ := exists_common_restriction Y n 0 z
  refine ⟨a, ?_⟩
  have h0 : z + pull (knPrY Y (n + 1)) 0 a = 0 := by
    refine mvExactZero (hemiU Y n) (hemiV Y n) (hemi_sup Y n) ?_ ?_
    · rw [map_add, mvResU_pull_knPrY, hU, add_self_eq_zero_two _]
    · rw [map_add, mvResV_pull_knPrY, hV, add_self_eq_zero_two _]
  have := congrArg (fun y => y + pull (knPrY Y (n + 1)) 0 a) h0
  simpa only [add_assoc, add_self_eq_zero_two _, add_zero, zero_add] using this

end KnHemi

end

end GroupApproximation.CharClass
