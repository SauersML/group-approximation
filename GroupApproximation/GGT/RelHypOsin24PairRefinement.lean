import GroupApproximation.GGT.RelHypOsin24ContinuationData

/-!
# The source action frontier for the general Osin--Hull specialization

The quotient construction only needs a Hull alphabet containing the original
relative alphabet on which Osin's two suitable witnesses are loxodromic.  Once
the witnesses are loxodromic, their non-commensurability gives independence by
the proved Morse estimate, and Osin suitability gives the finite-normalizer
clause.

`HyperbolicPairAcylindricalRefinementStatement` isolates the remaining source
geometry.  It has no quotient, relator, kernel, target, or image-family clause:
it is the element-classification part of Osin's relative theory combined with
the acylindrical enlargement of Theorem 5.4.  The empty-family theorem below
checks the statement on the ordinary finite-Cayley specialization.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- **Osin's hyperbolic-element classification through an acylindrical
refinement, at two prescribed elements.**

The output alphabet contains the labelled relative alphabet and keeps both
infinite-order non-parabolic elements loxodromic. -/
def HyperbolicPairAcylindricalRefinementStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.base.Finite → D.IsHyperbolicallyEmbedded →
      ∀ f₁ f₂ : G,
        IsHyperbolicElement D.fam f₁ →
        IsHyperbolicElement D.fam f₂ →
        (∀ n : ℕ, 0 < n → f₁ ^ n ≠ 1) →
        (∀ n : ℕ, 0 < n → f₂ ^ n ≠ 1) →
          ∃ (A : Alphabet G) (delta : ℝ),
            D.alphabet.carrier ⊆ A.carrier ∧
              IsHyperbolicSpace delta (Cayley A) ∧
                IsAcylindrical G (Cayley A) ∧
                  IsLoxodromic f₁ (Cayley.base A) ∧
                    IsLoxodromic f₂ (Cayley.base A)

/-- The refinement statement's empty-family model is the original finite
Cayley alphabet. -/
theorem exists_hyperbolicPairAcylindricalRefinement_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (f₁ f₂ : G)
    (hord₁ : ∀ n : ℕ, 0 < n → f₁ ^ n ≠ 1)
    (hord₂ : ∀ n : ℕ, 0 < n → f₂ ^ n ≠ 1) :
    ∃ (A : Alphabet G) (delta : ℝ),
      D.alphabet.carrier ⊆ A.carrier ∧
        IsHyperbolicSpace delta (Cayley A) ∧
          IsAcylindrical G (Cayley A) ∧
            IsLoxodromic f₁ (Cayley.base A) ∧
              IsLoxodromic f₂ (Cayley.base A) := by
  obtain ⟨delta, hdelta⟩ := hemb.hyperbolic
  exact ⟨D.alphabet, delta, Set.Subset.rfl, hdelta,
    relHypFiniteBaseAcylindricity_empty D hfinite,
    relHypHyperbolicElementLoxodromic_empty D hfinite hemb f₁ hord₁,
    relHypHyperbolicElementLoxodromic_empty D hfinite hemb f₂ hord₂⟩

/-- The continuation-data form of the compatible action frontier. -/
def CompatibleRelativeHullContinuationStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v)
    (Hfam : I → Subgroup G), IsRelativelyHyperbolic G Hfam →
      ∀ H : Subgroup G, IsSuitableSubgroup Hfam H →
        Nonempty (RelativeHullContinuationData Hfam H)

/-- Preserving the two suitable witnesses through an acylindrical refinement
constructs the complete initial continuation datum. -/
theorem compatibleRelativeHullContinuationStatement_of_pairRefinement
    (hrefine : HyperbolicPairAcylindricalRefinementStatement.{u, v}) :
    CompatibleRelativeHullContinuationStatement.{u, v} := by
  intro G instG I Hfam hrel H hsuit
  letI : Group G := instG
  obtain ⟨D, hfinite, hfam, hemb⟩ := hrel
  have hnormal : HullSuitable.NormalizesNoNontrivialFinite H :=
    IsSuitableSubgroup.normalizesNoNontrivialFinite hsuit
  obtain ⟨f₁, hf₁, f₂, hf₂, hhyper₁, hhyper₂,
    hord₁, hord₂, hnc, _hinter⟩ := hsuit
  have hhyper₁D : IsHyperbolicElement D.fam f₁ := by
    rw [hfam]
    exact hhyper₁
  have hhyper₂D : IsHyperbolicElement D.fam f₂ := by
    rw [hfam]
    exact hhyper₂
  obtain ⟨A, delta, hcontain, hdelta, hacy, hlox₁, hlox₂⟩ :=
    hrefine G instG I D hfinite hemb f₁ f₂ hhyper₁D hhyper₂D
      hord₁ hord₂
  have hnoPower : ∀ p q : ℤ, p ≠ 0 → q ≠ 0 → f₁ ^ p ≠ f₂ ^ q := by
    intro p q hp hq heq
    apply hnc
    refine ⟨p, q, 1, hp, hq, ?_⟩
    simpa using heq
  have hindTheory : Elementary.IndependentOfNoCommonZpow G (Cayley.base A) :=
    ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic
      A hdelta hacy
  have hind : Independent f₁ f₂ (Cayley.base A) :=
    hindTheory f₁ f₂ hlox₁ hlox₂ hnoPower
  have hactsH : ActsNonElementarily H (Cayley.base A) :=
    ⟨f₁, hf₁, f₂, hf₂, hlox₁, hlox₂, hind⟩
  have hactsTop : ActsNonElementarily (⊤ : Subgroup G) (Cayley.base A) :=
    ⟨f₁, Subgroup.mem_top f₁, f₂, Subgroup.mem_top f₂,
      hlox₁, hlox₂, hind⟩
  let B : HullGeneratingSet G :=
    { alphabet := A
      delta := delta
      hyperbolic := hdelta
      acylindrical := hacy
      nonElementary := hactsTop }
  have hHullSuitable : Suitable B.alphabet H := ⟨hactsH, hnormal⟩
  exact ⟨{
    rel := D
    base_finite := hfinite
    fam_eq := hfam
    embedded := hemb
    hull := B
    rel_alphabet_subset := hcontain
    suitable := hHullSuitable }⟩

/-- The equality-based compatible action implies the continuation-data form. -/
theorem compatibleRelativeHullContinuationStatement_of_compatibleAction
    (haction : CompatibleRelativeHullActionStatement.{u, v}) :
    CompatibleRelativeHullContinuationStatement.{u, v} := by
  intro G instG I Hfam hrel H hsuit
  obtain ⟨B⟩ := haction G instG I Hfam hrel H hsuit
  exact ⟨B.toContinuation⟩

end RelHyp
end GGT
end GroupApproximation
