import GroupApproximation.CharClass.CohomologyChartSplit
import GroupApproximation.CharClass.CohomologyDeltaNatural

/-!
# `cpTop` is pulled back from the projective factor

`cc-projective` conjectured that the connecting-map class `cpTop` is not merely
comparable to the pulled-back tautological generator but **equal** to it, which
would delete the triangular change of basis.  They could not check it because it
turns on how `interSigma` factors, which is on this side.

It does factor.  `interSigma` is the sphere generator pulled back along the
composite intersection → sphere, and that composite goes through
`cc-projective`'s own intersection: `interHomotopyEquiv` is
`prodSubtypeHomeo` followed by the identity on the base times their
`interSphereHomotopyEquiv`, so taking the sphere component is taking the second
coordinate first.  With `mvDelta_naturality` along the projection to the
projective factor — whose preimage cover is the chart cover on the nose — `cpTop`
is therefore the pullback of a class on `ℂP^{d+1}` that does not mention the base
at all.

## Main declarations

* `KnCP.interSigmaPt`, `KnCP.cpTopPt` — the same two classes with no base factor.
* `KnCP.interSigma_eq_pull`, `KnCP.cpTop_eq_pull_cpTopPt`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The sphere generator of `cc-projective`'s intersection, with no base factor. -/
def interSigmaPt : Hmod2 (interSpace d) (2 * d + 1) :=
  pull (cmap (interSphereHomotopyEquiv d).toFun) (2 * d + 1)
    (sphereTopClass (2 * d + 1) (by omega))

/-- The connecting-map class of `cc-projective`'s cover, with no base factor. -/
def cpTopPt : Hmod2 (CPtop (d + 1)) (2 * d + 1 + 1) :=
  (mvDelta (chartOpen d) (punctOpen d) (chartOpen_sup_punctOpen d)
    (2 * d + 1)).hom (interSigmaPt d)

/-- The sphere component of the intersection identification is the second
coordinate followed by `cc-projective`'s. -/
theorem interHE_comp_knPrS :
    cmap (interHomotopyEquiv U d).toFun ≫ knPrS U (2 * d + 1)
      = interToInterSpace U d ≫ cmap (interSphereHomotopyEquiv d).toFun := by
  apply TopCat.Hom.ext
  ext p
  rfl

/-- **`interSigma` is pulled back from `cc-projective`'s intersection.** -/
theorem interSigma_eq_pull :
    interSigma U d = pull (interToInterSpace U d) (2 * d + 1) (interSigmaPt d) := by
  rw [interSigma, knSigma, ← pull_comp, interHE_comp_knPrS, pull_comp, interSigmaPt]

/-- The chart cover is the preimage of `cc-projective`'s under the projection. -/
theorem interToInterSpace_eq_interRestrict :
    interToInterSpace U d
      = interRestrict (cpPrCP U d) (chartOpen d) (punctOpen d) := rfl

/-- **`cpTop` is pulled back from the projective factor**, so it does not depend on
the base at all. -/
theorem cpTop_eq_pull_cpTopPt :
    cpTop U d = pull (cpPrCP U d) (2 * d + 1 + 1) (cpTopPt d) := by
  rw [cpTop, interSigma_eq_pull, interToInterSpace_eq_interRestrict]
  exact MVDelta.mvDelta_naturality (cpPrCP U d) (chartOpen d) (punctOpen d)
    (chartOpen_sup_punctOpen d) (2 * d + 1) (interSigmaPt d)

/-! ## The rank-two identification -/

set_option maxHeartbeats 1000000 in
/-- **Uniqueness of the `cpTop`-coefficient at rank two**, unconditionally: at
`d = 0` flatness is `exists_flat_zero` and needs no hypothesis. -/
theorem cpTop_cup_injective_zero (m : ℕ) (b : Hmod2 (TopCat.of U) m)
    (h : cup (cpTop U 0) (pull (cpPrU U 0) m b) = 0) : b = 0 := by
  have hb : (mvDelta (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1 + m)).hom
      (cup (interSigma U 0) (pull (cpPrSub U 0 (interUSet U 0)) m b)) = 0 := by
    have hc := MVDelta.mvDelta_cup (chartU U 0) (punctU U 0) (cp_sup U 0)
      (interSigma U 0) (pull (cpPrU U 0) m b)
    rw [pull_sInclusion_cpPrU] at hc
    rw [hc, show (mvDelta (chartU U 0) (punctU U 0) (cp_sup U 0)
      (2 * 0 + 1)).hom (interSigma U 0) = cpTop U 0 from rfl, h, cohCast_zero]
  obtain ⟨a', b', hab⟩ :=
    (mvExactW (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1 + m) _).1 hb
  obtain ⟨e₁, he₁⟩ := exists_pull_cpPrSub_chart U 0 (2 * 0 + 1 + m) a'
  obtain ⟨e₂, he₂⟩ := exists_flat_zero U (2 * 0 + 1 + m) b'
  have hflat : cup (interSigma U 0) (pull (cpPrSub U 0 (interUSet U 0)) m b)
      = pull (cpPrSub U 0 (interUSet U 0)) (2 * 0 + 1 + m) (e₁ + e₂) := by
    rw [← hab, ← he₁, mvResWU_pull_cpPrSub, he₂, pull_add]
  have hsphere : cup (knSigma U (2 * 0 + 1) (by omega))
        (pull (knPrY U (2 * 0 + 1)) m b)
      = pull (knPrY U (2 * 0 + 1)) (2 * 0 + 1 + m) (e₁ + e₂) := by
    refine (interPullEquiv U 0 (2 * 0 + 1 + m)).injective ?_
    show pull (cmap (interHomotopyEquiv U 0).toFun) (2 * 0 + 1 + m) _
      = pull (cmap (interHomotopyEquiv U 0).toFun) (2 * 0 + 1 + m) _
    rw [pull_cup, pull_interHE_prU, pull_interHE_prU]
    exact hflat
  refine KnHemi.kunneth_decomposition_unique U (2 * 0 + 1) (by omega)
    (2 * 0 + 1 + m) m rfl 0 (e₁ + e₂) b 0 ?_
  rw [pull_zero, zero_add, cohCast_self, cohCast_self, pull_zero, cup_zero, add_zero]
  exact hsphere

theorem cpTopPt_zero_ne_zero : cpTopPt 0 ≠ 0 := by
  intro h0
  haveI : Nonempty ↥(TopCat.of Unit) := ⟨()⟩
  have hz : cup (cpTop Unit 0) (pull (cpPrU Unit 0) 0 (one (TopCat.of Unit))) = 0 := by
    rw [cpTop_eq_pull_cpTopPt, h0, pull_zero, zero_cup]
  exact one_ne_zero_cohZero (TopCat.of Unit)
    (cpTop_cup_injective_zero Unit 0 (one (TopCat.of Unit)) hz)

/-- **At rank two `cpTop` IS the tautological generator, pulled back.**  So the
triangular change of basis `cc-projective` was prepared to write does not exist:
there is nothing to change. -/
theorem cpTopPt_zero_eq_cpGen : cpTopPt 0 = cpGen 1 (by omega) :=
  eq_cpGen_of_ne_zero (by omega) cpTopPt_zero_ne_zero

theorem cpTop_zero_eq_pull_cpGen :
    cpTop U 0 = pull (cpPrCP U 0) 2 (cpGen 1 (by omega)) := by
  rw [cpTop_eq_pull_cpTopPt, cpTopPt_zero_eq_cpGen]

end KnCP

end

end GroupApproximation.CharClass
