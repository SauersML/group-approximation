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

/-- The preserved relative alphabet lies in the image of the source relative
alphabet together with the allowed enlargement. -/
theorem canonicalPreserved_alphabet_carrier_subset_image
    {G : Type u} [Group G] {I : Type v} {Q : Type u} [Group Q]
    {q : G →* Q} {D : RelGenSet G I} {Y : Set G}
    (P : HullSC.CanonicalQuotientFamilyPreservation q D Y) :
    P.rel.alphabet.carrier ⊆ q '' (D.alphabet.carrier ∪ Y) :=
  P.alphabet_carrier_subset_image

end RelHyp
end GGT
end GroupApproximation
