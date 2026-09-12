import GroupApproximation.CharClass.LerayHirschRankOne

/-!
# Leray–Hirsch at rank one, over any coefficient ring

The coefficient-generic form of `LerayHirschRankOne`.  At rank one the projectivisation *is* the
base (`projRankOneHomeo`) and the projection witnesses it (`projMapOf_eq_isoHom`, coefficient-free),
so pullback along the projection is bijective in every degree over any `K` and the column has one
entry.  No field is needed and no class is used: the statement holds for every `ξ`.

## Main declarations

* `bijective_pull_projMapOf_rankOneOf` — at rank one the projection is bijective on cohomology.
* `hasFreeTuple_rankOneOf`, `lerayHirschGraded_rankOneOf` — **Leray–Hirsch at rank one, over `K`**.
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

/-- **At rank one the projection is bijective on cohomology**, over any coefficient ring. -/
theorem bijective_pull_projMapOf_rankOneOf (K : Type) [CommRing K] (q : Bundle X ι)
    (hq : ∀ x, (q x).trace = 1) (n : ℕ) :
    Function.Bijective (pull (K := K) (projMapOf q) n) := by
  rw [projMapOf_eq_isoHom q hq]
  exact bijective_pull_iso _ n

/-- **The free-module statement at rank one**, over any coefficient ring.  One entry, and it is
the pullback. -/
theorem hasFreeTuple_rankOneOf (K : Type) [CommRing K] (q : Bundle X ι)
    (hq : ∀ x, (q x).trace = 1) (ξ : Hmod K (TopCat.of (Proj q)) 2) :
    HasFreeTuple (projMapOf q) ξ 1 := by
  intro n
  have hb := bijective_pull_projMapOf_rankOneOf K q hq n
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

/-- **Leray–Hirsch at rank one**, over any coefficient ring and for every class. -/
theorem lerayHirschGraded_rankOneOf (K : Type) [CommRing K] (q : Bundle X ι)
    (hq : ∀ x, (q x).trace = 1) (ξ : Hmod K (TopCat.of (Proj q)) 2) :
    LerayHirschGraded (projMapOf q) ξ 1 :=
  lerayHirschGraded_of_bijective _ _ _ fun n =>
    bijective_lhSum_of_freeTuple _ _ _ (hasFreeTuple_rankOneOf K q hq ξ) n

end

end LH
end CharClass
end GroupApproximation
