import GroupApproximation.CharClass.LerayHirschFiniteOf
import GroupApproximation.CharClass.LerayHirschBundle

/-!
# Leray–Hirsch for a bundle over a compact base, over a field

The coefficient-generic form of `LerayHirschBundle.lerayHirschGraded_of_trivializing_cover`.  The
trivialising sets, their finiteness on a compact base and the fold recognising a cover carry no
coefficients (`trivOpen`, `Bundle.exists_finite_trivializing_cover`, `foldr_sup_eq_top`), so the
proof is the `F₂` one with the finite-cover induction replaced by `lerayHirschGraded_of_finite_coverOf`.

## Main declarations

* `lerayHirschGraded_of_trivializing_coverOf` — **Leray–Hirsch for a bundle over a compact base,
  over a field**, over the trivialising-open hypothesis.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace

noncomputable section

namespace LH

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

variable {P : TopCat.{0}}

/-- **Leray–Hirsch for a bundle over a compact base, over a field.**  The trivialising sets cover
and compactness makes the cover finite; the predicate "contained in a trivialising set" is closed
under intersection, which is what the induction on the cover demands. -/
theorem lerayHirschGraded_of_trivializing_coverOf (K : Type) [Field K] [CompactSpace X]
    [Nonempty X] (p : Bundle X ι) (f : P ⟶ TopCat.of X) (ξ : Hmod K P 2) (r : ℕ)
    (hLH : ∀ (x₀ : X) (W : Opens (TopCat.of X)), LHOver f ξ r (trivOpen p x₀ ⊓ W)) :
    LerayHirschGraded f ξ r := by
  classical
  obtain ⟨s, hs⟩ := Bundle.exists_finite_trivializing_cover p
  refine lerayHirschGraded_of_finite_coverOf K f ξ r
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
