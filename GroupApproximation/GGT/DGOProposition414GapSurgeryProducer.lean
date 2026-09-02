import GroupApproximation.GGT.DGOProposition414GapIntervalProducer
import GroupApproximation.GGT.DGOProposition414SurgeryReduction

/-!
# Exact residual input for balanced interval surgery

The interval family, inherited-arc quasigeodesicity, and both individual child
bounds are canonical.  This module isolates the remaining component, charging,
and global counting geometry and turns it directly into the realization used
by the landed Proposition 4.14 reduction.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The exact geometric residue after constructing the canonical gap interval
family.

**This route is not being pursued.**  It and the component-family route reach
the same linear `SumBound`, and the component-family route is the smaller of
the two: `FirstGapComponentFamily.ofTargetComponents` already reduces all four
of its fields to a single all-target component family, and
`gapComponentConfigurations_of_targetIsolated` and
`exists_gapComponentConfigurations_of_targetIsolated` are landed against it.
This route additionally owes `TwoHalfDistributedFactorPlacement`, whose
`leftSlot`, `middleSlot`, `rightSlot`, `factorization`, `slots_disjoint` and
`sources_disjoint` are all unbuilt, and the two aggregate counts.  The code is
kept because `intervalSurgery`, `realization` and `sumBound_linear_of_gapCompletion`
are correct and would be wanted again if the component-family route stalled. -/
structure BalancedSplitGapCompletion
    (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n) {k R : ℕ}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  components : BalancedSplitData.GapComponentConfigurations hsymm hδ P B
  factorGeometry : TwoHalfDistributedFactorPlacement D hsymm b hδ
    (B.gapIntervalsOfConfigurations components).toPathInput.family
    P.target P.label P.span
  count_lower : n ≤
    (∑ j, (((B.gapIntervalsOfConfigurations components).toPathInput).first j).sideCount) +
      ∑ j, (((B.gapIntervalsOfConfigurations components).toPathInput).second j).sideCount
  count_upper :
    (∑ j, (((B.gapIntervalsOfConfigurations components).toPathInput).first j).sideCount) +
        ∑ j, (((B.gapIntervalsOfConfigurations components).toPathInput).second j).sideCount ≤
      n + 6 * ((2 * B.chord.length + 1) * (2 * B.chord.length + 1))

namespace BalancedSplitGapCompletion

/-- Fill every field of balanced interval surgery from the exact residual
geometry. -/
noncomputable def intervalSurgery
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (S : BalancedSplitGapCompletion D hsymm b hδ P B) :
    BalancedSplitIntervalSurgery D hsymm b hδ P B where
  intervals := B.gapIntervalsOfConfigurations S.components
  factorGeometry := S.factorGeometry
  count_lower := S.count_lower
  count_upper := S.count_upper
  first_side_bound := B.gapIntervalsOfConfigurations_first_side_bound
    S.components
  second_side_bound := B.gapIntervalsOfConfigurations_second_side_bound
    S.components

/-- The residual completion is sufficient for the realization premise of the
uniform Proposition 4.14 reduction. -/
noncomputable def realization
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (S : BalancedSplitGapCompletion D hsymm b hδ P B) :
    BalancedSplitSurgeryRealization D hsymm b hδ P B where
  surgery := S.intervalSurgery

/-- Existential form consumed verbatim by
`sumBound_linear_of_balancedSurgery`. -/
theorem nonempty_realization
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (S : BalancedSplitGapCompletion D hsymm b hδ P B) :
    Nonempty (BalancedSplitSurgeryRealization D hsymm b hδ P B) :=
  ⟨S.realization⟩

end BalancedSplitGapCompletion

/-- The uniform Proposition 4.14 conclusion now needs only the exact residual
gap completion on each balanced split. -/
theorem sumBound_linear_of_gapCompletion
    (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
        Nonempty (BalancedSplitGapCompletion D hsymm b hδ P B)) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) := by
  apply sumBound_linear_of_balancedSurgery D hsymm b hδ
  intro n k R P B
  obtain ⟨S⟩ := produce P B
  exact S.nonempty_realization

end DGOProposition414
end GGT
end GroupApproximation
