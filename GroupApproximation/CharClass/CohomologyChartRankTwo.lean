import GroupApproximation.CharClass.CohomologyChartFlatBase

/-!
# The projective-factor Künneth at the bottom: a `ℂP^1` factor

At `d = 0` the loop that blocks the general case does not arise.  The punctured
piece is `U × ℂP^0`, which is `U`, so the restriction to it is surjective outright
— a class on it is a pullback from `U`, and a pullback from `U` on the whole
product restricts to it.  With the kernel statement already landed, that gives the
decomposition with a `ℂP^1` fibre:

```text
z = pr_U^* a + cpTop ⌣ pr_U^* b
```

This is the rank-two Leray–Hirsch base case.  `cc-projective` converts it to the
form in powers of the tautological class by a triangular change of basis, which
costs nothing at rank two because both classes sit in degree two and differ by a
pullback from `U`; the general rank goes through the ring structure, which is
downstream of this theorem rather than upstream.

## Main results

* `KnCP.mvResV_surjective_zero` — the restriction is onto at `d = 0`.
* `KnCP.decomposition_zero` — the decomposition with a `ℂP^1` factor.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U]

/-- **The restriction to the punctured piece is onto at the bottom.** -/
theorem mvResV_surjective_zero (k : ℕ) (w : Hmod2 (TopCat.of ↥(punctUSet U 0)) k) :
    ∃ z : Hmod2 (cpProdTop U 0) k,
      (mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) k).hom z = w := by
  obtain ⟨c, hc⟩ := exists_pull_cpPrSub_punct_zero U k w
  exact ⟨pull (cpPrU U 0) k c, by rw [mvResV_pull_cpPrU, hc]⟩

set_option maxHeartbeats 1000000 in
/-- **The Künneth decomposition with a `ℂP^1` factor.** -/
theorem decomposition_zero (m : ℕ)
    (z : Hmod2 (cpProdTop U 0) (2 * 0 + 1 + m + 1)) :
    ∃ (a : Hmod2 (TopCat.of U) (2 * 0 + 1 + m + 1)) (b : Hmod2 (TopCat.of U) m),
      z = pull (cpPrU U 0) (2 * 0 + 1 + m + 1) a
        + cohCast (aw_degree_left_succ (2 * 0 + 1) m)
            (cup (cpTop U 0) (pull (cpPrU U 0) m b)) := by
  obtain ⟨a, ha⟩ := exists_pull_cpPrSub_punct_zero U (2 * 0 + 1 + m + 1)
    ((mvResV (chartU U 0) (punctU U 0) (cp_sup U 0) (2 * 0 + 1 + m + 1)).hom z)
  have hz : (mvResV (chartU U 0) (punctU U 0) (cp_sup U 0)
      (2 * 0 + 1 + m + 1)).hom
      (z + pull (cpPrU U 0) (2 * 0 + 1 + m + 1) a) = 0 := by
    rw [map_add, mvResV_pull_cpPrU, ha, add_self_eq_zero_two]
  obtain ⟨b, hb⟩ := exists_of_mvResV_eq_zero U 0 m _ hz
  refine ⟨a, b, ?_⟩
  rw [← hb, add_comm z, ← add_assoc, add_self_eq_zero_two, zero_add]

end KnCP

end

end GroupApproximation.CharClass
