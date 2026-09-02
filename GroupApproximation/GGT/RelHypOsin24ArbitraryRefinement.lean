import GroupApproximation.GGT.RelHypOsin24PairRefinement
import GroupApproximation.GGT.OsinTheorem54Unconditional

/-!
# The arbitrary-index acylindrical enlargement

Osin's Theorem 5.4 is proved in this repository for a finite peripheral index.
For the arbitrary-index relative structure used by the verbatim Theorem 2.4,
the acylindrical part of the source refinement can still be obtained without a
finite-index assumption: apply Theorem 5.4 to the empty labelled family whose
base is the entire original relative alphabet.  Its output alphabet contains
that alphabet and has a hyperbolic, acylindrical Cayley action.

This file isolates that strictly smaller geometric estimate.  It does not
claim that the two prescribed non-parabolic elements remain loxodromic on this
enlargement.  That is the remaining arbitrary-index classification step in
`HyperbolicPairAcylindricalRefinementStatement`; adding a source element as a
base letter shows why loxodromy cannot be inferred from alphabet inclusion,
hyperbolicity, and acylindricity alone.

The empty-family theorem is the model test: when there are no peripheral
labels and the original base is finite, the original finite Cayley graph
already supplies the acylindrical action.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- **Arbitrary-index acylindrical enlargement.**  The output contains the
labelled relative alphabet, but no loxodromic witness is requested. -/
def ArbitraryFamilyAcylindricalEnlargementStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.IsHyperbolicallyEmbedded →
      ∃ (A : Alphabet G) (delta : ℝ),
        D.alphabet.carrier ⊆ A.carrier ∧
          IsHyperbolicSpace delta (Cayley A) ∧
            IsAcylindrical G (Cayley A)

/-! ## The empty labelled family used by the enlargement -/

def emptyFamilyRelGenSet {G : Type u} [Group G] {I : Type v}
    (D : RelGenSet G I) : RelGenSet G Empty where
  base := D.alphabet.carrier
  fam := Empty.elim
  symmetricGenerating := by
    change IsSymmetricGeneratingSet
      (D.alphabet.carrier ∪
        ⋃ e : Empty, ((Empty.elim e : Subgroup G) : Set G))
    rw [Set.iUnion_of_empty, Set.union_empty]
    exact D.alphabet.symmetricGenerating

theorem emptyFamilyRelGenSet_alphabet {G : Type u} [Group G] {I : Type v}
    (D : RelGenSet G I) :
    (emptyFamilyRelGenSet D).alphabet = D.alphabet := by
  apply OsinComponents.alphabet_eq_of_carrier_eq
  change D.alphabet.carrier ∪
      ⋃ e : Empty, ((Empty.elim e : Subgroup G) : Set G) = D.alphabet.carrier
  rw [Set.iUnion_of_empty, Set.union_empty]

theorem emptyFamilyRelGenSet_embedded {G : Type u} [Group G] {I : Type v}
    (D : RelGenSet G I) (hD : D.IsHyperbolicallyEmbedded) :
    (emptyFamilyRelGenSet D).IsHyperbolicallyEmbedded := by
  refine ⟨?_, ?_⟩
  · rw [emptyFamilyRelGenSet_alphabet D]
    exact hD.hyperbolic
  · intro e
    exact Empty.elim e

/-! ## The estimate and its finite empty-family model -/

/-- The empty-family application of Osin's Theorem 5.4 proves the arbitrary
index enlargement estimate. -/
theorem arbitraryFamilyAcylindricalEnlargement_proved :
    ArbitraryFamilyAcylindricalEnlargementStatement.{u, v} := by
  intro G instG I D hD
  letI : Group G := instG
  obtain ⟨E, hbase, _hfam, hE, hacy⟩ :=
    OsinEnlargement.osinTheorem54Fam_unconditional G Empty
      (emptyFamilyRelGenSet D) (emptyFamilyRelGenSet_embedded D hD)
  obtain ⟨delta, hdelta⟩ := hE.hyperbolic
  have hcontain : D.alphabet.carrier ⊆ E.alphabet.carrier := by
    intro x hx
    exact Or.inl (hbase hx)
  exact ⟨E.alphabet, delta, hcontain, hdelta, hacy⟩

/-- In the empty-family finite-Cayley model no enlargement is needed. -/
theorem arbitraryFamilyAcylindricalEnlargement_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite)
    (hD : D.IsHyperbolicallyEmbedded) :
    ∃ (A : Alphabet G) (delta : ℝ),
      D.alphabet.carrier ⊆ A.carrier ∧
        IsHyperbolicSpace delta (Cayley A) ∧
          IsAcylindrical G (Cayley A) := by
  obtain ⟨delta, hdelta⟩ := hD.hyperbolic
  exact ⟨D.alphabet, delta, Set.Subset.rfl, hdelta,
    relHypFiniteBaseAcylindricity_empty D hfinite⟩

end RelHyp
end GGT
end GroupApproximation
