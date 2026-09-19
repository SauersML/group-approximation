import GroupApproximation.CharClass.LerayHirschLadderClosed
import GroupApproximation.CharClass.LerayHirschChartClassGen
import GroupApproximation.CharClass.BundleReindex

/-!
# Leray–Hirsch at rank one

The compact-base instance is stated uniformly in the rank, but its proof is not.
For rank `s` the fibre of the projectivisation is `ℂP^{s-1}` and the chart step needs
that dimension to be at least one; at rank one the fibre is a point and there is no
chart step to run.

What is true there is stronger, and comes from `cc-bundle` directly: the
projectivisation of a rank-one bundle *is* the base, by `projRankOneHomeo`, and the
projection is what witnesses it.  So the column has one entry and the whole content
is that the pullback is bijective.

`cc-wu`'s flag tower runs down to rank one at its last stage, so this branch is
exercised rather than vacuous.

## Main declarations

* `projMapOf_eq_isoHom` — at rank one the projection *is* the homeomorphism.
* `hasFreeTuple_rankOne`, `lerayHirschGraded_rankOne` — **Leray–Hirsch at rank one**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.CharClass.Bundle

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At rank one the projection is the homeomorphism, as a morphism.  Stated rather
than left to unification: the two are pointwise `rfl`, but checking it as an
`isDefEq` between morphisms times out. -/
theorem projMapOf_eq_isoHom (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    projMapOf q = (TopCat.isoOfHomeo (projRankOneHomeo q hq)).hom :=
  TopCat.hom_ext (ContinuousMap.ext fun z => (projRankOneHomeo_over_base q hq z).symm)

/-- **At rank one the projection is bijective on cohomology.** -/
theorem bijective_pull_projMapOf_rankOne (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1)
    (n : ℕ) : Function.Bijective (pull (projMapOf q) n) := by
  rw [projMapOf_eq_isoHom q hq]
  exact bijective_pull_iso _ n

/-- **The free-module statement at rank one.**  One entry, and it is the pullback. -/
theorem hasFreeTuple_rankOne (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1)
    (ξ : Hmod2 (TopCat.of (Proj q)) 2) : HasFreeTuple (projMapOf q) ξ 1 := by
  intro n
  have hb := bijective_pull_projMapOf_rankOne q hq n
  refine ⟨fun z => ?_, fun a _ hzero i => ?_⟩
  · obtain ⟨x, hx⟩ := hb.2 z
    refine ⟨fun i => cohCast (show n = n - 2 * (i : ℕ) by have := i.2; omega) x,
      fun i hi => absurd hi (by have := i.2; omega), ?_⟩
    rw [Fin.sum_univ_one]
    show z = lhTerm (projMapOf q) ξ n 0
      (cohCast (show n = n - 2 * ((0 : Fin 1) : ℕ) by omega) x)
    rw [lhTerm_zero_index, pull_cohCast, cohCast_self]
    exact hx.symm
  · rw [Fin.sum_univ_one] at hzero
    have h0 : lhTerm (projMapOf q) ξ n 0 (a 0) = 0 := hzero
    rw [lhTerm_zero_index] at h0
    have : a 0 = 0 := hb.1 (by rw [h0, pull_zero])
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    rw [hi]
    exact this

/-- **Leray–Hirsch at rank one.** -/
theorem lerayHirschGraded_rankOne (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1)
    (ξ : Hmod2 (TopCat.of (Proj q)) 2) :
    LerayHirschGraded (projMapOf q) ξ 1 :=
  lerayHirschGraded_of_freeTuple _ _ _ (hasFreeTuple_rankOne q hq ξ)

end

end LH
end CharClass
end GroupApproximation
