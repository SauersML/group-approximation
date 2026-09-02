import GroupApproximation.GGT.RelHypOsin24PairRefinement
import GroupApproximation.GGT.RelHypOsin24AcylindricalRefinement
import GroupApproximation.GGT.RelHypOsin24ClassificationBridge

/-!
# Hyperbolic elements on labelled relative Cayley graphs

For a hyperbolically embedded family, an infinite-order element not conjugate
into a peripheral subgroup is loxodromic on the relative Cayley graph.  This is
the element-classification lemma used after Osin's Theorem 5.4 enlargement.

The reduction below proves that, for a finite peripheral index, this one
classification statement supplies the complete two-witness refinement needed
by the Osin--Hull construction.  The family equality in Theorem 5.4 preserves
non-parabolicity, and inclusion of its enlarged base gives inclusion of the
whole original labelled relative alphabet.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- **Osin's classification of infinite-order hyperbolic elements.** -/
def HyperbolicElementLoxodromicStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.IsHyperbolicallyEmbedded → ∀ g : G,
      IsHyperbolicElement D.fam g →
        (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          IsLoxodromic g (Cayley.base D.alphabet)

/-- Osin's one-element classification is reduced to the strictly smaller
relative power escape estimate.  The reduction first applies Theorem 5.4 to
the empty labelled family, then uses the acylindrical Bowditch bridge and
finally descends loxodromy along the alphabet inclusion. -/
theorem hyperbolicElementLoxodromicStatement_of_relativePowerEscape
    (hEscape : RelativePowerEscapeStatement.{u, v}) :
    HyperbolicElementLoxodromicStatement.{u, v} := by
  exact hyperbolicElementLoxodromic_of_relativePowerEscape hEscape

/-- The classification statement holds in its finite-Cayley empty-family
model. -/
theorem hyperbolicElementLoxodromic_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (g : G)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsLoxodromic g (Cayley.base D.alphabet) :=
  relHypHyperbolicElementLoxodromic_empty D hfinite hemb g hord

/-- At a finite peripheral family, element classification after Osin's
Theorem 5.4 gives the prescribed two-element acylindrical refinement. -/
theorem exists_hyperbolicPairAcylindricalRefinement_of_classification_finite
    (hclass : HyperbolicElementLoxodromicStatement.{u, v})
    {G : Type u} [Group G] {I : Type v} [Finite I]
    (D : RelGenSet G I) (hemb : D.IsHyperbolicallyEmbedded)
    (f₁ f₂ : G) (hhyper₁ : IsHyperbolicElement D.fam f₁)
    (hhyper₂ : IsHyperbolicElement D.fam f₂)
    (hord₁ : ∀ n : ℕ, 0 < n → f₁ ^ n ≠ 1)
    (hord₂ : ∀ n : ℕ, 0 < n → f₂ ^ n ≠ 1) :
    ∃ (A : Alphabet G) (delta : ℝ),
      D.alphabet.carrier ⊆ A.carrier ∧
        IsHyperbolicSpace delta (Cayley A) ∧
          IsAcylindrical G (Cayley A) ∧
            IsLoxodromic f₁ (Cayley.base A) ∧
              IsLoxodromic f₂ (Cayley.base A) := by
  obtain ⟨E⟩ := exists_acylindricalRelativeRefinement D hemb
  obtain ⟨delta, hdelta⟩ := E.embedded.hyperbolic
  have hcontain : D.alphabet.carrier ⊆ E.rel.alphabet.carrier := by
    rintro x (hx | hx)
    · exact Set.mem_union_left _ (E.base_subset hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, by
        rw [E.fam_eq]
        exact hi⟩)
  have hhyper₁E : IsHyperbolicElement E.rel.fam f₁ := by
    rw [E.fam_eq]
    exact hhyper₁
  have hhyper₂E : IsHyperbolicElement E.rel.fam f₂ := by
    rw [E.fam_eq]
    exact hhyper₂
  exact ⟨E.rel.alphabet, delta, hcontain, hdelta, E.acylindrical,
    hclass G inferInstance I E.rel E.embedded f₁ hhyper₁E hord₁,
    hclass G inferInstance I E.rel E.embedded f₂ hhyper₂E hord₂⟩

end RelHyp
end GGT
end GroupApproximation
