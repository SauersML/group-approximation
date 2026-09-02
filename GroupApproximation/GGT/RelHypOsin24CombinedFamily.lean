import GroupApproximation.GGT.RelHypDefinition
import GroupApproximation.GGT.HullEeLocalFiniteness
import GroupApproximation.GGT.OsinTheorem54SepSymmetric

/-!
# Combining the original and selected Osin peripheral families

In the Hull specialization of Osin's Theorem 2.4 there are two labelled
families.  `D` is the original relatively hyperbolic family over its finite
base `X`.  `E` is the finite family of elementary closures selected inside the
suitable subgroup, hyperbolically embedded over the full relative alphabet of
`D`.  The family used by Hull Lemmas 4.4 and 4.9 is their labelled sum, still
over the finite base `X`.

This module constructs that sum and proves all definitional parts of the DGO
transitivity bridge.  Its relative alphabet is exactly the alphabet of `E`
when `E.base = D.alphabet.carrier`.  The only geometric statement isolated
below is DGO Proposition 4.35, transitivity of hyperbolic embeddedness.  It is
strictly smaller than Osin's quotient theorem: it mentions no quotient,
relator, suitable subgroup, or target.

The empty-right-family lemmas are model checks for the construction: adjoining
no selected peripherals changes neither the labelled family nor the relative
alphabet.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## The labelled sum -/

/-- The original family and a selected family, both retained with their own
indices, over the original relative base. -/
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

/-- Every original relative letter value remains in the combined alphabet. -/
theorem original_alphabet_subset_combined
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) :
    D.alphabet.carrier ⊆ (combinedRelGenSet D E).alphabet.carrier := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩)

/-- Every selected peripheral lies in the combined relative alphabet. -/
theorem selected_fam_subset_combined
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K) (k : K) :
    (E.fam k : Set G) ⊆ (combinedRelGenSet D E).alphabet.carrier := by
  intro x hx
  exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr k, hx⟩)

/-! ## Equality of the two full alphabets -/

/-- If the selected family is embedded over the original full relative
alphabet, its alphabet and the combined-family alphabet have the same carrier. -/
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

/-- The equality upgraded from carriers to the bundled alphabets. -/
theorem combined_alphabet_eq
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K)
    (hbase : E.base = D.alphabet.carrier) :
    (combinedRelGenSet D E).alphabet = E.alphabet := by
  apply OsinComponents.alphabet_eq_of_carrier_eq
  exact combined_alphabet_carrier_eq D E hbase

/-! ## The geometric transitivity frontier -/

/-- **DGO Proposition 4.35, labelled family form.**

If the original family is hyperbolically embedded over `X`, and the selected
family is hyperbolically embedded over `X ⊔ №`, then their labelled union is
hyperbolically embedded over `X`.  This is the exact transitivity step used in
the proof of Osin's Theorem 2.4 before applying Hull's one-step quotient. -/
def DGOFamilyTransitivityStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (K : Type w)
    (D : RelGenSet G I) (E : RelGenSet G K),
    D.IsHyperbolicallyEmbedded →
      E.base = D.alphabet.carrier →
      E.IsHyperbolicallyEmbedded →
        (combinedRelGenSet D E).IsHyperbolicallyEmbedded

/-- The transitivity conclusion has exactly the selected Cayley graph as its
hyperbolic graph; only local finiteness of the two labelled halves is geometric. -/
theorem combined_hyperbolic_of_selected
    {G : Type u} [Group G] {I : Type v} {K : Type w}
    (D : RelGenSet G I) (E : RelGenSet G K)
    (hbase : E.base = D.alphabet.carrier)
    (hE : E.IsHyperbolicallyEmbedded) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (combinedRelGenSet D E).alphabet) := by
  rw [combined_alphabet_eq D E hbase]
  exact hE.hyperbolic

/-- The empty selected index has no right-hand peripheral labels, so the sum
construction's family is pointwise the original family.  This is the smallest
model of the labelled combination. -/
theorem combined_emptyRight_fam
    {G : Type u} [Group G] {I : Type v}
    (D : RelGenSet G I) (E : RelGenSet G Empty) (s : Sum I Empty) :
    (combinedRelGenSet D E).fam s = D.fam (Equiv.sumEmpty I Empty s) := by
  cases s with
  | inl i => rfl
  | inr k => exact Empty.elim k

end RelHyp
end GGT
end GroupApproximation
