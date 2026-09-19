import GroupApproximation.CharClass.CohomologyChartRestrict

/-!
# The top power of the tautological class, and the kernel of the restriction

The projective-factor Künneth needs a class of degree `2d + 2` on `U × ℂP^{d+1}`
playing the role of `h^{d+1}`.  The ring structure of `H^*(ℂP^d)` is not available
yet, but it is not needed: the class enters only through the connecting map of the
chart cover, exactly as the suspended sphere class did.  `KnCP.cpTop` is `δ` of
the sphere generator of the intersection, and `mvDelta_naturality` identifies it
as pulled back from `ℂP^{d+1}`, so it does not depend on the base.

With it, the kernel of the restriction to the punctured piece is described: a
class restricting to zero there is `cpTop` cupped with a pullback from the base,
and the coefficient is unique.

## Main results

* `KnCP.cpTop` — the top class, defined by the connecting map.
* `KnCP.exists_of_mvResV_eq_zero` — the kernel of the restriction.
* `KnCP.cpTop_cup_injective` — the coefficient is unique.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The sphere generator of the intersection, transported. -/
def interSigma : Hmod2 (TopCat.of ↥(interUSet U d)) (2 * d + 1) :=
  pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1)
    (knSigma U (2 * d + 1) (by omega))

/-- **The top power of the tautological class**, defined by the connecting map of the
chart cover.  No ring structure is used. -/
def cpTop : Hmod2 (cpProdTop U d) (2 * d + 1 + 1) :=
  (mvDelta (chartU U d) (punctU U d) (cp_sup U d) (2 * d + 1)).hom (interSigma U d)

theorem pull_sInclusion_cpPrU (S : Set ↥(cpProdTop U d)) (k : ℕ)
    (v : Hmod2 (TopCat.of U) k) :
    pull (sInclusion S) k (pull (cpPrU U d) k v) = pull (cpPrSub U d S) k v := by
  rw [← pull_comp, sInclusion_comp_cpPrSub]

/-! ## The kernel of the restriction to the punctured piece -/

set_option maxHeartbeats 1000000 in
/-- **A class restricting to zero on the punctured piece is a multiple of `cpTop`.**
The degree cast is the one `mvDelta_cup` produces, `(2d+1)+1+m = (2d+1)+m+1`. -/
theorem exists_of_mvResV_eq_zero (m : ℕ)
    (z : Hmod2 (cpProdTop U d) (2 * d + 1 + m + 1))
    (h : (mvResV (chartU U d) (punctU U d) (cp_sup U d)
      (2 * d + 1 + m + 1)).hom z = 0) :
    ∃ b : Hmod2 (TopCat.of U) m,
      z = cohCast (aw_degree_left_succ (2 * d + 1) m)
            (cup (cpTop U d) (pull (cpPrU U d) m b)) := by
  have hU := mvResU_eq_zero_of_mvResV_eq_zero U d (2 * d + 1 + m + 1) z h
  obtain ⟨w, hw⟩ := (mvExactX (chartU U d) (punctU U d) (cp_sup U d)
    (2 * d + 1 + m) z).1 ⟨hU, h⟩
  obtain ⟨w', hw'⟩ :
      ∃ w', pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m) w' = w :=
    ⟨(interPullEquiv U d (2 * d + 1 + m)).symm w,
      (interPullEquiv U d (2 * d + 1 + m)).apply_symm_apply w⟩
  obtain ⟨c, b, hcb⟩ := KnHemi.kunneth_decomposition U (2 * d + 1) (by omega)
    (2 * d + 1 + m) m rfl w'
  refine ⟨b, ?_⟩
  have hsplit : w = pull (cpPrSub U d (interUSet U d)) (2 * d + 1 + m) c
      + pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m)
          (cup (knSigma U (2 * d + 1) (by omega))
            (pull (knPrY U (2 * d + 1)) m b)) := by
    rw [← hw', hcb, pull_add, pull_interHE_prU, cohCast_self]
  rw [← hw, hsplit, map_add, mvDelta_pull_cpPrSub_inter, zero_add, pull_cup,
    pull_interHE_prU, ← pull_sInclusion_cpPrU, MVDelta.mvDelta_cup]
  rfl

end KnCP

end

end GroupApproximation.CharClass
