import GroupApproximation.CharClass.CohomologyChartFlatOf
import GroupApproximation.CharClass.CohomologyChartTautClass
import GroupApproximation.CharClass.CohomologyDeltaNaturalOf
import GroupApproximation.CharClass.CohomologyTotalNontrivialOf

/-!
# `cpTopOf` is pulled back from the projective factor, over a field

The coefficient-generic forms of `CohomologyChartTautClass`: the connecting-map class of the chart
cover of `U × ℂP^{d+1}` is the pullback of a class on `ℂP^{d+1}` with no base factor, and at rank
two it detects pullbacks from the base.  The maps (`interToInterSpace`, `interSphereHomotopyEquiv`,
`interRestrict`) and their compatibilities carry no coefficients and are the `F₂` file's own.

## Main declarations

* `KnCP.interSigmaPtOf`, `KnCP.cpTopPtOf` — the two classes with no base factor.
* `KnCP.interSigmaOf_eq_pull`, `KnCP.cpTopOf_eq_pull_cpTopPtOf`.
* `KnCP.cpTop_cup_injective_zeroOf` — **uniqueness of the `cpTopOf`-coefficient at rank two**.
* `KnCP.cpTopPtOf_zero_ne_zero`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The sphere generator of `cc-projective`'s intersection over `K`, with no base factor. -/
def interSigmaPtOf : Hmod K (interSpace d) (2 * d + 1) :=
  pull (cmap (interSphereHomotopyEquiv d).toFun) (2 * d + 1)
    (sphereTopClassOf K (2 * d + 1) (by omega))

/-- The connecting-map class of `cc-projective`'s cover over `K`, with no base factor. -/
def cpTopPtOf : Hmod K (CPtop (d + 1)) (2 * d + 1 + 1) :=
  (mvDeltaOf K (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)
    (2 * d + 1)).hom (interSigmaPtOf K d)

/-- **`interSigmaOf` is pulled back from `cc-projective`'s intersection.** -/
theorem interSigmaOf_eq_pull :
    interSigmaOf K U d = pull (interToInterSpace U d) (2 * d + 1) (interSigmaPtOf K d) := by
  rw [interSigmaOf, knSigmaOf, ← pull_comp, interHE_comp_knPrS, pull_comp, interSigmaPtOf]

/-- **`cpTopOf` is pulled back from the projective factor**, over `K`. -/
theorem cpTopOf_eq_pull_cpTopPtOf :
    cpTopOf K U d = pull (cpPrCP U d) (2 * d + 1 + 1) (cpTopPtOf K d) := by
  rw [cpTopOf, interSigmaOf_eq_pull, interToInterSpace_eq_interRestrict]
  exact MVDelta.mvDeltaOf_naturality K (cpPrCP U d) (chartOpen d) (punctOpen d)
    (chartOpen_sup_punctOpen d) (2 * d + 1) (interSigmaPtOf K d)

set_option maxHeartbeats 1000000 in
/-- **Uniqueness of the `cpTopOf`-coefficient at rank two**, over `K` and unconditionally: at
`d = 0` flatness is `exists_flat_zeroOf`. -/
theorem cpTop_cup_injective_zeroOf (m : ℕ) (b : Hmod K (TopCat.of U) m)
    (h : cup (cpTopOf K U 0) (pull (cpPrU U 0) m b) = 0) : b = 0 := by
  have hb : (mvDeltaOf K (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1 + m)).hom
      (cup (interSigmaOf K U 0) (pull (cpPrSub U 0 (interUSet U 0)) m b)) = 0 := by
    have hc := MVDelta.mvDeltaOf_cup K (chartU U 0) (punctU U 0) (cp_sup U 0)
      (interSigmaOf K U 0) (pull (cpPrU U 0) m b)
    rw [pull_sInclusion_cpPrUOf] at hc
    rw [hc, show (mvDeltaOf K (chartU U 0) (punctU U 0) (cp_sup U 0)
      (2 * 0 + 1)).hom (interSigmaOf K U 0) = cpTopOf K U 0 from rfl, h, cohCast_zero]
  obtain ⟨a', b', hab⟩ :=
    (mvExactWOf K (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1 + m) _).1 hb
  obtain ⟨e₁, he₁⟩ := exists_pull_cpPrSub_chartOf K U 0 (2 * 0 + 1 + m) a'
  obtain ⟨e₂, he₂⟩ := exists_flat_zeroOf K U (2 * 0 + 1 + m) b'
  have hflat : cup (interSigmaOf K U 0) (pull (cpPrSub U 0 (interUSet U 0)) m b)
      = pull (cpPrSub U 0 (interUSet U 0)) (2 * 0 + 1 + m) (e₁ + e₂) := by
    rw [← hab, ← he₁, mvResWUOf_pull_cpPrSub, he₂, pull_add]
  have hsphere : cup (knSigmaOf K U (2 * 0 + 1) (by omega))
        (pull (knPrY U (2 * 0 + 1)) m b)
      = pull (knPrY U (2 * 0 + 1)) (2 * 0 + 1 + m) (e₁ + e₂) := by
    refine (interPullEquivOf K U 0 (2 * 0 + 1 + m)).injective ?_
    show pull (cmap (interHomotopyEquiv U 0).toFun) (2 * 0 + 1 + m) _
      = pull (cmap (interHomotopyEquiv U 0).toFun) (2 * 0 + 1 + m) _
    rw [pull_cup, pull_interHE_prUOf, pull_interHE_prUOf]
    exact hflat
  refine KnHemi.kunneth_decomposition_uniqueOf K U (2 * 0 + 1) (by omega)
    (2 * 0 + 1 + m) m rfl 0 (e₁ + e₂) b 0 ?_
  rw [pull_zero, zero_add, cohCast_self, cohCast_self, pull_zero, cup_zero, add_zero]
  exact hsphere

/-- The connecting-map class of the cover of `ℂP^1` is nonzero, over `K`. -/
theorem cpTopPtOf_zero_ne_zero : cpTopPtOf K 0 ≠ 0 := by
  intro h0
  haveI : Nonempty ↥(TopCat.of Unit) := ⟨()⟩
  have hz : cup (cpTopOf K Unit 0) (pull (cpPrU Unit 0) 0 (one (TopCat.of Unit))) = 0 := by
    rw [cpTopOf_eq_pull_cpTopPtOf, h0, pull_zero, zero_cup]
  exact one_ne_zero_cohZeroOf K (TopCat.of Unit)
    (cpTop_cup_injective_zeroOf K Unit 0 (one (TopCat.of Unit)) hz)

end KnCP

end

end GroupApproximation.CharClass
