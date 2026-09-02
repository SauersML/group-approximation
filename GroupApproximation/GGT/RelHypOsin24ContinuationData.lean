import GroupApproximation.GGT.RelHypOsin24Action
import GroupApproximation.GGT.HullSCLemma44FamilyStatement

/-!
# Relative/Hull data stable under successive fillings

The first Osin filling may use the relative and Hull alphabets literally equal.
Hull Lemma 5.8 can enlarge the quotient Hull alphabet, while the image of the
original finite relative base must be retained to prove relative hyperbolicity
with a finite base.  `RelativeHullContinuationData` separates those roles and
asks only that the relative alphabet be contained in the Hull alphabet.

The equality-based `RelativeHullData` converts to this structure.  The second
lemma identifies the alphabet in a canonical preserved-family quotient with
the image of the source relative alphabet; together these facts let the data
iterate after every one-relator filling.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- A finite-base relative structure and a containing Hull alphabet on which
the distinguished subgroup is suitable. -/
structure RelativeHullContinuationData
    {G : Type u} [Group G] {I : Type v}
    (Hfam : I → Subgroup G) (H : Subgroup G) where
  rel : RelGenSet G I
  base_finite : rel.base.Finite
  fam_eq : rel.fam = Hfam
  embedded : rel.IsHyperbolicallyEmbedded
  hull : HullGeneratingSet G
  rel_alphabet_subset : rel.alphabet.carrier ⊆ hull.alphabet.carrier
  suitable : Suitable hull.alphabet H

/-- Equality of the initial alphabets gives continuation data. -/
def RelativeHullData.toContinuation
    {G : Type u} [Group G] {I : Type v} {Hfam : I → Subgroup G}
    {H : Subgroup G} (B : RelativeHullData Hfam H) :
    RelativeHullContinuationData Hfam H where
  rel := B.rel
  base_finite := B.base_finite
  fam_eq := B.fam_eq
  embedded := B.embedded
  hull := B.hull
  rel_alphabet_subset := by rw [← B.hull_alphabet]
  suitable := B.suitable

/-- The preserved relative alphabet is exactly the image of the source
relative alphabet. -/
theorem canonicalPreserved_alphabet_carrier_eq_image
    {G : Type u} [Group G] {I : Type v} {Q : Type u} [Group Q]
    {q : G →* Q} {D : RelGenSet G I}
    (P : HullSC.CanonicalQuotientFamilyPreservation q D) :
    P.rel.alphabet.carrier = q '' D.alphabet.carrier := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · rw [P.base_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, Set.mem_union_left _ hx, rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      rw [P.fam_map i] at hi
      obtain ⟨x, hx, rfl⟩ := hi
      exact ⟨x, Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, hx⟩), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · exact Set.mem_union_left _ (by
        rw [P.base_map]
        exact ⟨x, hx, rfl⟩)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, by
        rw [P.fam_map i]
        exact Subgroup.mem_map_of_mem q hi⟩)

end RelHyp
end GGT
end GroupApproximation
