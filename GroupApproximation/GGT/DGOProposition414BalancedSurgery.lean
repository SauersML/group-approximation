import GroupApproximation.GGT.DGOProposition414SubarcInterval
import GroupApproximation.GGT.DGOProposition414IntervalTargetSlots
import GroupApproximation.GGT.DGOProposition414EntryOwner
import GroupApproximation.GGT.DGOProposition414GapSurvivors
import GroupApproximation.GGT.DGOProposition414GapArcComponents

/-!
# Exact interval surgery over a balanced split

This file is the bookkeeping boundary between the two geometric halves and
the exact Proposition 4.14 producer.  The interval geometry is indexed by the
canonical broken-component assignment.  The charging certificate records the
child-by-source target packets arising from surviving sides and
broken-component quadrilaterals.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The concrete interval paths and side accounting produced by component
surgery on both halves of a balanced split. -/
structure BalancedSplitIntervalSurgery
    (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n) {k R : ℕ}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  intervals : TwoHalfIntervalSurgery D hsymm b B.brokenAssignment.index
    B.firstBase (vertex P.basepoint P.word B.secondVertex)
    B.chord B.chord_geodesic
  factorGeometry : TwoHalfDistributedFactorPlacement D hsymm b hδ
    intervals.toPathInput.family P.target P.label P.span
  count_lower : n ≤
    (∑ j, ((intervals.toPathInput).first j).sideCount) +
      ∑ j, ((intervals.toPathInput).second j).sideCount
  count_upper :
    (∑ j, ((intervals.toPathInput).first j).sideCount) +
        ∑ j, ((intervals.toPathInput).second j).sideCount ≤
      n + 6 * ((2 * B.chord.length + 1) * (2 * B.chord.length + 1))
  first_side_bound : ∀ j,
    ((intervals.toPathInput).first j).sideCount ≤
      (B.secondSide - B.firstSide + 1) + B.chord.length
  second_side_bound : ∀ j,
    ((intervals.toPathInput).second j).sideCount ≤
      (n - B.secondSide) + B.firstSide + 1 + B.chord.length

namespace BalancedSplitIntervalSurgery

/-- The balanced split uses the original chord itself, so the corrected
`SideBounds` chord-length field is definitional. -/
theorem sideBounds
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (S : BalancedSplitIntervalSurgery D hsymm b hδ P B)
    (hfirstSmall : ∀ j,
      5 * ((S.intervals.toPathInput).first j).sideCount ≤ 4 * n)
    (hsecondSmall : ∀ j,
      5 * ((S.intervals.toPathInput).second j).sideCount ≤ 4 * n) :
    TwoHalfIntervalSurgery.SideBounds S.intervals n where
  count_lower := S.count_lower
  count_upper := S.count_upper
  first_small := hfirstSmall
  second_small := hsecondSmall

/-- The distributed child-side packets supply the complete two-half charging
configuration, including the quadrilateral radius and finite-sum arguments. -/
noncomputable def configuration
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (S : BalancedSplitIntervalSurgery D hsymm b hδ P B) :
    TwoHalfChargingConfiguration D hsymm b hδ
      S.intervals.toPathInput.family P.target P.label P.span :=
  S.factorGeometry.configuration

/-- The general charging certificate and the exact side accounting assemble
into the family certificate consumed by Proposition 4.14. -/
noncomputable def certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (S : BalancedSplitIntervalSurgery D hsymm b hδ P B)
    (hfirstSmall : ∀ j,
      5 * ((S.intervals.toPathInput).first j).sideCount ≤ 4 * n)
    (hsecondSmall : ∀ j,
      5 * ((S.intervals.toPathInput).second j).sideCount ≤ 4 * n) :
    AuxiliaryCycleFamilyCertificate D hsymm b hδ n P.basepoint P.word P.cut
      P.target P.label := by
  let counts := TwoHalfSideAccounting.ofPathLengthBounds
    (TwoHalfIntervalSurgery.toPathLengthBounds
      (S.sideBounds hfirstSmall hsecondSmall))
  exact auxiliaryCycleFamilyCertificate_of_twoHalf D hsymm b hδ
    B.brokenAssignment.index S.intervals.toPathInput.family n P.basepoint
    P.word P.cut P.target P.label S.configuration counts.count_lower
    counts.count_upper counts.first_small counts.second_small

/-- On an extremal polygon, the exact balanced-surgery certificate exports the
numerical subdivision tuple used by the corrected Proposition 4.14 assembly. -/
theorem exists_quadraticCostSubdivisionData
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (S : BalancedSplitIntervalSurgery D hsymm b hδ P B)
    (hfirstSmall : ∀ j,
      5 * ((S.intervals.toPathInput).first j).sideCount ≤ 4 * n)
    (hsecondSmall : ∀ j,
      5 * ((S.intervals.toPathInput).second j).sideCount ≤ 4 * n)
    (hextremal : ∀ r : ℕ → ℕ,
      (∀ s ∈ P.target,
        P.span s ∈ D.relBall (P.label s) (r s)) →
      sumCost D hsymm b hδ n ≤ ∑ s ∈ P.target, r s) :
    ∃ (childCount : ℕ) (childSides : Fin childCount → ℕ)
        (chordLength : ℕ) (partners : List ℕ),
      sumCost D hsymm b hδ n ≤
        ∑ i, sumCost D hsymm b hδ (childSides i) ∧
      n ≤ ∑ i, childSides i ∧
      (ChordPartnerQuadraticTraversalBound chordLength partners →
        ∑ i, childSides i ≤ n + 6 * (chordLength * chordLength)) ∧
      (∀ i, 5 * childSides i ≤ 4 * n) ∧
      ChordPartnerQuadraticTraversalBound chordLength partners :=
  exists_quadraticCostSubdivisionData_of_extremalFamily D hsymm b hδ P
    hextremal (S.certificate hfirstSmall hsecondSmall)

end BalancedSplitIntervalSurgery

end DGOProposition414
end GGT
end GroupApproximation
