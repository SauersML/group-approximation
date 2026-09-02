import GroupApproximation.GGT.DGOProposition414GapCompletionProducer

/-!
# Uniform Proposition 4.14 from classwise gap certificates

The balanced-surgery reduction already proves that a nonempty
`BalancedSplitGapCompletion` at every raw split yields one linear constant for
all side counts.  This module instantiates that reduction with the classwise
first- and second-family certificates, giving the uniform isolated-component
sum bound of Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The classwise bisection certificates imply the uniform Proposition 4.14
sum bound. -/
theorem uniformSumBound_of_gapCertificates
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : DGOProposition414.BalancedSplitData D hsymm b hδ P k R),
      Nonempty (DGOProposition414.BalancedSplitData.FirstGapTargetCertificate B) ∧
      Nonempty (DGOProposition414.BalancedSplitData.SecondGapTargetCertificate B)) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  apply sumBound_linear_of_gapCompletion D hsymm b hδ
  intro n k R P B
  obtain ⟨first, second⟩ := produce P B
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨B.gapCompletion_of_certificates first second⟩

end DGOProposition414
end GGT
end GroupApproximation
