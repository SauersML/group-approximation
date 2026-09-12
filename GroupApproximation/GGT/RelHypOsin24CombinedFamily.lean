import GroupApproximation.GGT.RelHypDefinition
import GroupApproximation.GGT.OsinTheorem54SepSymmetric

/-!
# The labelled sum of original and selected peripheral families

The quotient proof uses two families: the original relatively hyperbolic
family and the finite family of selected elementary closures.  This module
contains only their algebraic labelled sum and the equality of its alphabet
with the selected relative alphabet when that alphabet uses the original full
alphabet as its base.

No transitivity theorem is asserted here.  DGO Proposition 4.35 has additional
finiteness hypotheses in the direction relevant to the application, so the
arbitrary-family preservation statement belongs in Hull Lemma 4.4's interface
rather than in this construction.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

universe u v w

/-- The labelled sum of an original and a selected peripheral family, using
the original relative base. -/
def combinedRelGenSet {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) : RelGenSet G (Sum I K) where
  base := D.base
  fam
    | Sum.inl i => D.fam i
    | Sum.inr k => E.fam k
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · have hi := D.symmetricGenerating.inv_mem x (Or.inl hx)
        rcases hi with hi | hi
        · exact Or.inl hi
        · obtain ⟨i, hii⟩ := Set.mem_iUnion.mp hi
          exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl i, hii⟩)
      · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
        cases s with
        | inl i =>
            exact Or.inr (Set.mem_iUnion.mpr
              ⟨Sum.inl i, (D.fam i).inv_mem hs⟩)
        | inr k =>
            exact Or.inr (Set.mem_iUnion.mpr
              ⟨Sum.inr k, (E.fam k).inv_mem hs⟩)
    · refine eq_top_iff.mpr ?_
      rw [← D.symmetricGenerating.closure_eq]
      apply Subgroup.closure_mono
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩)

@[simp] theorem combinedRelGenSet_base
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) :
    (combinedRelGenSet D E).base = D.base := rfl

@[simp] theorem combinedRelGenSet_fam_inl
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) (i : I) :
    (combinedRelGenSet D E).fam (Sum.inl i) = D.fam i := rfl

@[simp] theorem combinedRelGenSet_fam_inr
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) (k : K) :
    (combinedRelGenSet D E).fam (Sum.inr k) = E.fam k := rfl

/-- Every original relative letter remains a letter after adjoining the
selected family. -/
theorem original_alphabet_subset_combined
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) :
    D.alphabet.carrier ⊆ (combinedRelGenSet D E).alphabet.carrier := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩)

/-- Every selected peripheral is contained in the combined alphabet. -/
theorem selected_fam_subset_combined
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) (k : K) :
    (E.fam k : Set G) ⊆ (combinedRelGenSet D E).alphabet.carrier := by
  intro x hx
  exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr k, hx⟩)

/-- If the selected family is based on the original full alphabet, then its
full alphabet is exactly the alphabet of the labelled sum. -/
theorem combined_alphabet_carrier_eq
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K)
    (hbase : E.base = D.alphabet.carrier) :
    (combinedRelGenSet D E).alphabet.carrier = E.alphabet.carrier := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl (hbase.symm ▸ Or.inl hx)
    · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      cases s with
      | inl i =>
          exact Or.inl (hbase.symm ▸
            Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hs⟩))
      | inr k =>
          exact Or.inr (Set.mem_iUnion.mpr ⟨k, hs⟩)
  · intro hx
    rcases hx with hx | hx
    · rw [hbase] at hx
      exact original_alphabet_subset_combined D E hx
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact selected_fam_subset_combined D E k hk

/-- Bundled form of `combined_alphabet_carrier_eq`. -/
theorem combined_alphabet_eq
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K)
    (hbase : E.base = D.alphabet.carrier) :
    (combinedRelGenSet D E).alphabet = E.alphabet := by
  apply OsinComponents.alphabet_eq_of_carrier_eq
  exact combined_alphabet_carrier_eq D E hbase

end RelHyp
end GGT
end GroupApproximation
