import GroupApproximation.GGT.DGOProposition414GapSurgeryProducer
import GroupApproximation.GGT.DGOProposition414GapCountLower

/-!
# Numerical fields of balanced gap completion

The opposite-partner edge cover gives the lower child-side count, while the
arc, connector, and chord accounting gives the upper count.  This module
inserts those two proved inequalities into `BalancedSplitGapCompletion`, so
only the child component configurations and distributed factor placement
remain geometric inputs.  This is the counting part of the bisection step in
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitGapCompletion

/-- Construct a gap completion from its two geometric fields; both global
side-count fields are consequences of the canonical interval family. -/
noncomputable def ofGeometry
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (components : BalancedSplitData.GapComponentConfigurations hsymm hδ P B)
    (factorGeometry : TwoHalfDistributedFactorPlacement D hsymm b hδ
      (B.gapIntervalsOfConfigurations components).toPathInput.family
      P.target P.label P.span) :
    BalancedSplitGapCompletion D hsymm b hδ P B where
  components := components
  factorGeometry := factorGeometry
  count_lower := B.gapIntervalsOfConfigurations_count_lower components
  count_upper := B.gapIntervalsOfConfigurations_count_upper components

end BalancedSplitGapCompletion

/-- The uniform Proposition 4.14 conclusion follows once the two geometric
fields are produced on every balanced split. -/
theorem sumBound_linear_of_gapGeometry
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
        ∃ components : BalancedSplitData.GapComponentConfigurations
            hsymm hδ P B,
          Nonempty (TwoHalfDistributedFactorPlacement D hsymm b hδ
            (B.gapIntervalsOfConfigurations components).toPathInput.family
            P.target P.label P.span)) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  apply sumBound_linear_of_gapCompletion D hsymm b hδ
  intro n k R P B
  obtain ⟨components, ⟨factorGeometry⟩⟩ := produce P B
  exact ⟨BalancedSplitGapCompletion.ofGeometry components
    factorGeometry⟩

end DGOProposition414
end GGT
end GroupApproximation
