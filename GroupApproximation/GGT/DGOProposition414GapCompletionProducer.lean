import GroupApproximation.GGT.DGOProposition414GapTargetAssembly
import GroupApproximation.GGT.DGOProposition414DistributedFactorPlacement
import GroupApproximation.GGT.DGOProposition414GapCompletionCounts

/-!
# Balanced gap-completion producer

The four classwise target certificates are assembled into both complete child
component families.  The canonical three-slot factor placement then supplies
the charging geometry, while the lower and upper side-count theorems fill the
two numerical fields.  This is the exact residual producer required by the
balanced-surgery reduction for Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Assemble both complete families from classwise component and isolation
certificates. -/
noncomputable def gapComponentConfigurations_of_certificates
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (first : FirstGapTargetCertificate B)
    (second : SecondGapTargetCertificate B) :
    GapComponentConfigurations hsymm hδ P B where
  first := fun j => B.firstGapConfiguration_of_certificate first j
  second := fun j => B.secondGapConfiguration_of_certificate second j

/-- Construct all four fields of `BalancedSplitGapCompletion` from the two
classwise child certificates. -/
noncomputable def gapCompletion_of_certificates
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (first : FirstGapTargetCertificate B)
    (second : SecondGapTargetCertificate B) :
    BalancedSplitGapCompletion D hsymm b hδ P B := by
  let C := B.gapComponentConfigurations_of_certificates first second
  exact BalancedSplitGapCompletion.ofGeometry C
    (B.distributedFactorPlacement C)

/-- The classwise certificates provide the nonempty residual realization used
by the linear Proposition 4.14 reduction. -/
theorem nonempty_gapCompletion_of_certificates
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (first : FirstGapTargetCertificate B)
    (second : SecondGapTargetCertificate B) :
    Nonempty (BalancedSplitGapCompletion D hsymm b hδ P B) :=
  ⟨B.gapCompletion_of_certificates first second⟩

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
