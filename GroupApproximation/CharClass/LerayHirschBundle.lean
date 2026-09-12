import GroupApproximation.CharClass.LerayHirschUnion
import GroupApproximation.CharClass.BundleLocal
import GroupApproximation.CharClass.CohomologyProductBase
import GroupApproximation.CharClass.LIXSectionManuscript

/-!
# Leray–Hirsch for a bundle over a compact base

Two things.

`noOddCohomology_baseY` names, in the spelling the even side uses, the fact that
the program's base has no odd cohomology.  The single-factor case is
`noOddCohomology_CP` and the fold over a dependent product is
`cc-cohom-api`'s `KnCP.noOddCohomology_piCP`; this is only the restatement at
`baseY`, so that a consumer never has to unfold it.

`lerayHirschGraded_of_trivializing_cover` is the bundle-side half of the cover
induction.  The trivialising sets of the projection model are open and cover, so
compactness makes the cover finite; and the predicate "contained in a trivialising
set" is closed under intersection with anything, which is exactly what the
induction demands and what a trivialisation gives for free, since cutting a
trivialising set down leaves it trivialising.

The theorem takes Leray–Hirsch over each such set as a hypothesis.  That is the
one input still owed, and it is `cc-cohom-api`'s projective-factor Künneth read
through the chart trivialisation; nothing else about the bundle is used here.

## Main declarations

* `noOddCohomology_baseY` — the base has no odd cohomology.
* `trivOpen` — a trivialising set, as an open set.
* `lerayHirschGraded_of_trivializing_cover` — **Leray–Hirsch for a bundle over a
  compact base**, over the trivialising-open hypothesis.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace

noncomputable section

/-! ## 1. The base of the program has no odd cohomology -/

/-- **The program's base has no odd cohomology.**  A dependent product of complex
projective spaces, which is what `cc-lix-odd`'s `baseY` is. -/
theorem noOddCohomology_baseY {ℓ : ℕ} (dd : Fin ℓ → ℕ) :
    KnHemi.NoOddCohomology (baseY dd) :=
  KnCP.noOddCohomology_piCP ℓ dd

/-! ## 2. Leray–Hirsch over a trivialising cover -/

namespace LH

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A trivialising set of the bundle, as an open set. -/
def trivOpen (p : Bundle X ι) (x₀ : X) : Opens (TopCat.of X) :=
  ⟨Bundle.trivSet p x₀, Bundle.isOpen_trivSet p x₀⟩

variable {P : TopCat.{0}}

/-- **Leray–Hirsch for a bundle over a compact base.**  The trivialising sets cover
and compactness makes the cover finite; the predicate "contained in a trivialising
set" is closed under intersection, which is what the induction on the cover
demands. -/
theorem lerayHirschGraded_of_trivializing_cover [CompactSpace X] [Nonempty X]
    (p : Bundle X ι) (f : P ⟶ TopCat.of X) (ξ : Hmod2 P 2) (r : ℕ)
    (hLH : ∀ (x₀ : X) (W : Opens (TopCat.of X)), LHOver f ξ r (trivOpen p x₀ ⊓ W)) :
    LerayHirschGraded f ξ r := by
  classical
  obtain ⟨s, hs⟩ := Bundle.exists_finite_trivializing_cover p
  refine lerayHirschGraded_of_finite_cover f ξ r
    (fun A => ∃ (x₀ : X) (W : Opens (TopCat.of X)), A = trivOpen p x₀ ⊓ W)
    ?_ ?_ (s.toList.map (fun x₀ => trivOpen p x₀)) ?_ ⊥ ?_ ?_
  · rintro A W ⟨x₀, W', rfl⟩
    exact ⟨x₀, W' ⊓ W, by rw [inf_assoc]⟩
  · rintro A ⟨x₀, W, rfl⟩
    exact hLH x₀ W
  · intro B hB
    obtain ⟨x₀, _, rfl⟩ := List.mem_map.mp hB
    exact ⟨x₀, ⊤, by rw [inf_top_eq]⟩
  · exact ⟨Classical.arbitrary X, ⊥, by rw [inf_bot_eq]⟩
  · refine foldr_sup_eq_top _ _ fun x => ?_
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Or.inr ⟨trivOpen p t,
      List.mem_map.mpr ⟨t, Finset.mem_toList.mpr ht, rfl⟩, hxt⟩

end LH

end

end CharClass
end GroupApproximation
