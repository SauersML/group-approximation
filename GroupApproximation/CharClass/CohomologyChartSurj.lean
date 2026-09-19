import GroupApproximation.CharClass.CohomologyChartTop

/-!
# Surjectivity of the restriction to the punctured piece

The other half of the projective-factor Künneth.  A class on the punctured piece
extends to the whole product exactly when its restriction to the intersection is
pulled back from the base, by exactness at the middle term: the chart piece *is*
the base, so the classes on it restricting into the intersection are precisely the
pullbacks, and `mvExactSum` then matches the pair.

Below the sphere dimension that condition is automatic, because the intersection
is `U × S^{2d+1}` and `kunneth_low` says everything of degree under `2d + 1` there
is pulled back from `U`.  Since the tautological powers `h^i` with `i ≤ d` all sit
in degree `2i ≤ 2d`, this is the range in which the geometry of the covering map
would otherwise have had to be identified; the degree bound does that work
instead.

## Main results

* `KnCP.exists_flat_of_lt` — below `2d + 1`, everything on the intersection is a
  pullback from the base.
* `KnCP.mvResV_surjective_of_flat`, `KnCP.mvResV_surjective_of_lt`.
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

/-- **Below the sphere dimension the intersection is all pullbacks.** -/
theorem exists_flat_of_lt (k : ℕ) (hk : k < 2 * d + 1)
    (x : Hmod2 (TopCat.of ↥(interUSet U d)) k) :
    ∃ e : Hmod2 (TopCat.of U) k, x = pull (cpPrSub U d (interUSet U d)) k e := by
  obtain ⟨x', hx'⟩ :
      ∃ x', pull (cmap (interHomotopyEquiv U d).toFun) k x' = x :=
    ⟨(interPullEquiv U d k).symm x, (interPullEquiv U d k).apply_symm_apply x⟩
  obtain ⟨e, he⟩ := KnHemi.kunneth_low U (2 * d + 1) k hk x'
  refine ⟨e, ?_⟩
  rw [← hx', he, pull_interHE_prU]

set_option maxHeartbeats 1000000 in
/-- **A class on the punctured piece extends when its restriction to the intersection
is a pullback from the base.** -/
theorem mvResV_surjective_of_flat (k : ℕ)
    (w : Hmod2 (TopCat.of ↥(punctUSet U d)) k) (e : Hmod2 (TopCat.of U) k)
    (he : (mvResWV (chartU U d) (punctU U d) (cp_sup U d) k).hom w
      = pull (cpPrSub U d (interUSet U d)) k e) :
    ∃ z : Hmod2 (cpProdTop U d) k,
      (mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w := by
  obtain ⟨z, _, hz⟩ := (mvExactSum (chartU U d) (punctU U d) (cp_sup U d) k
    (pull (cpPrSub U d (chartUSet U d)) k e) w).1
    (by rw [mvResWU_pull_cpPrSub, he])
  exact ⟨z, hz⟩

set_option maxHeartbeats 1000000 in
/-- **Surjectivity of the restriction below the sphere dimension.** -/
theorem mvResV_surjective_of_lt (k : ℕ) (hk : k < 2 * d + 1)
    (w : Hmod2 (TopCat.of ↥(punctUSet U d)) k) :
    ∃ z : Hmod2 (cpProdTop U d) k,
      (mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w := by
  obtain ⟨e, he⟩ := exists_flat_of_lt U d k hk
    ((mvResWV (chartU U d) (punctU U d) (cp_sup U d) k).hom w)
  exact mvResV_surjective_of_flat U d k w e he

end KnCP

end

end GroupApproximation.CharClass
