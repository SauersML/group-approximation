import GroupApproximation.CharClass.ThomChernDegreewise
import GroupApproximation.CharClass.ThomFreeDegreewise
import GroupApproximation.CharClass.CohomologyLHRestrict
import GroupApproximation.CharClass.CohomologyKunnethHemi

/-!
# The restriction of a pair, in Leray–Hirsch coordinates

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/ThomFreeDegreewise.lean` computes the Thom class from an abstract
linear map `ThomDeg.restrictMap g`, and says in its own docstring that producing
`g` is somebody's topology.  This file produces it.

Over a projectivisation with a rank-`(r+1)` Leray–Hirsch instance upstairs and a
rank-`r` instance on the subspace, the restriction at the top degree `2r` is

```text
(a₀, …, a_r)  ↦  (a₀ + γ_r a_r, …, a_{r-1} + γ_1 a_r),
```

which is exactly `ThomDeg.restrictMap` at `g i = γ_{r-i} ⌣ ·`.  Two landed facts
do all the work: `LHCast.pull_lhTerm` carries a column term to a column term, and
`ThomChernDeg.lhTerm_top_eq_sum` rewrites the one column the subspace does not
have.

The ambient instance is **not** a hypothesis.  Only the subspace's is, because the
statement is about what the ambient combination restricts to, not about which
classes the combination reaches.

## Main declarations

* `absToSub_sum_lhTerm` — **the restriction square**, with the bottom edge
  `ThomDeg.restrictMap`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X P : TopCat.{0}}

/-- **The restriction of the pair, in Leray–Hirsch coordinates.**  The first `r`
coefficients are carried across unchanged, and the top one is folded into them by
the Chern relation on the subspace, which is exactly `ThomDeg.restrictMap` at
`g i = γ_{r-i} ⌣ ·`.

The ambient Leray–Hirsch instance is not a hypothesis: the statement is about what
an ambient combination restricts to, not about which classes such combinations
reach. -/
theorem absToSub_sum_lhTerm (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod2 P 2) (ξ' : Hmod2 (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (L' : LerayHirschGraded π' ξ' r)
    (a : (i : Fin (r + 1)) → Hmod2 X (2 * r - 2 * (i : ℕ))) :
    (absToSub (ZMod 2) Z (2 * r)).hom
        (∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i))
      = ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ)
          (ThomDeg.restrictMap (R := ZMod 2)
            (M := fun i : Fin (r + 1) => Hmod2 X (2 * r - 2 * (i : ℕ)))
            (fun i => chernMul L' i) a i) := by
  have hterm : ∀ i : Fin (r + 1),
      pull (sInclusion Z) (2 * r) (lhTerm π ξ (2 * r) (i : ℕ) (a i))
        = lhTerm π' ξ' (2 * r) (i : ℕ) (a i) :=
    fun i => LHCast.pull_lhTerm (sInclusion Z) π π' hπ ξ ξ' hξ (2 * r) (i : ℕ) (a i)
  have hlast : lhTerm π' ξ' (2 * r) ((Fin.last r : Fin (r + 1)) : ℕ) (a (Fin.last r))
      = ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ) (chernMul L' i (a (Fin.last r))) :=
    lhTerm_top_eq_sum L' (a (Fin.last r))
  rw [absToSub_eq_cohPullback, cohPullback_apply_eq, pull_sum]
  simp only [hterm]
  rw [Fin.sum_univ_castSucc, hlast, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (lhTerm_add π' ξ' (2 * r) (i : ℕ) (a i.castSucc)
    (chernMul L' i (a (Fin.last r)))).symm

/-! Printed on every build. -/

#print axioms absToSub_sum_lhTerm

end ThomChernDeg

end

end GroupApproximation.CharClass
