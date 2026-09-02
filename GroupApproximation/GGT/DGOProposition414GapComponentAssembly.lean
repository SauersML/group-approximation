import GroupApproximation.GGT.DGOProposition414GapIntervalProducer
import GroupApproximation.GGT.DGOProposition414FiniteComponentFile

/-!
# Component files for the balanced-split gap children

The bisection in Dahmani--Guirardel--Osin Proposition 4.14 produces, for each
gap child, a full-cycle component and isolation assertion for every inherited,
charged, and connector target.  This module turns those assertions into the
`AuxiliaryCycleComponentConfiguration` required by the interval producer.
The finite-start constructor enumerates all same-label component starts, so its
`exhaust` and `separated` fields are the full-cycle maximality and separation
clauses used by the auxiliary-cycle isolation theorem.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

noncomputable abbrev firstGapCycle
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :=
  auxiliaryCycleWord (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j))

noncomputable abbrev firstGapCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) (s : ℕ) :=
  auxiliaryCycleCut (B.firstGapLeft j)
    (B.firstGapFinishSide j - B.firstGapStartSide j)
    (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
      B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j) s

noncomputable abbrev secondGapCycle
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :=
  auxiliaryCycleWord (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j))

noncomputable abbrev secondGapCut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (s : ℕ) :=
  auxiliaryCycleCut (B.secondGapLeft j)
    (B.secondGapFinishSide j - B.secondGapStartSide j)
    (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
      B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j) s

noncomputable abbrev firstGapTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : Finset ℕ :=
  B.firstGapLocalTarget j ∪ auxiliaryCycleConnectorTarget
    (B.firstGapLeft j) (B.firstGapRight j)
    (B.firstGapFinishSide j - B.firstGapStartSide j)

noncomputable abbrev secondGapTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : Finset ℕ :=
  B.secondGapLocalTarget j ∪ auxiliaryCycleConnectorTarget
    (B.secondGapLeft j) (B.secondGapRight j)
    (B.secondGapFinishSide j - B.secondGapStartSide j)

/-- Materialize the first child component file from the four-path geometric
component and isolation assertions of Proposition 4.14. -/
noncomputable def firstGapConfiguration_of_targetIsolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (htarget : ∀ s ∈ B.firstGapTarget j,
      IsComp (B.firstGapLocalLabel j s) (B.firstGapCycle j)
        (B.firstGapCut j s) (B.firstGapCut j (s + 1)))
    (hiso : ∀ s ∈ B.firstGapTarget j,
      IsIsolated D.fam (B.firstGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) (B.firstGapCut j s)) :
    B.FirstGapComponentConfiguration j :=
  AuxiliaryCycleComponentConfiguration.ofTargetIsolated htarget hiso

/-- Materialize a wrapped-half child component file from the corresponding
four-path assertions of Proposition 4.14. -/
noncomputable def secondGapConfiguration_of_targetIsolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (htarget : ∀ s ∈ B.secondGapTarget j,
      IsComp (B.secondGapLocalLabel j s) (B.secondGapCycle j)
        (B.secondGapCut j s) (B.secondGapCut j (s + 1)))
    (hiso : ∀ s ∈ B.secondGapTarget j,
      IsIsolated D.fam (B.secondGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) (B.secondGapCut j s)) :
    B.SecondGapComponentConfiguration j :=
  AuxiliaryCycleComponentConfiguration.ofTargetIsolated htarget hiso

/-- Assemble both component families once the two child geometric outputs are
available at every gap. -/
noncomputable def gapComponentConfigurations_of_targetIsolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (firstTarget : ∀ j, ∀ s ∈ B.firstGapTarget j,
      IsComp (B.firstGapLocalLabel j s) (B.firstGapCycle j)
        (B.firstGapCut j s) (B.firstGapCut j (s + 1)))
    (firstIsolated : ∀ j, ∀ s ∈ B.firstGapTarget j,
      IsIsolated D.fam (B.firstGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.firstGapChordFinish j))
        (B.firstGapCycle j) (B.firstGapCut j s))
    (secondTarget : ∀ j, ∀ s ∈ B.secondGapTarget j,
      IsComp (B.secondGapLocalLabel j s) (B.secondGapCycle j)
        (B.secondGapCut j s) (B.secondGapCut j (s + 1)))
    (secondIsolated : ∀ j, ∀ s ∈ B.secondGapTarget j,
      IsIsolated D.fam (B.secondGapLocalLabel j s)
        (vertex B.firstBase B.chord (B.secondGapChordFinish j))
        (B.secondGapCycle j) (B.secondGapCut j s)) :
    GapComponentConfigurations hsymm hδ P B where
  first := fun j => B.firstGapConfiguration_of_targetIsolated j
    (firstTarget j) (firstIsolated j)
  second := fun j => B.secondGapConfiguration_of_targetIsolated j
    (secondTarget j) (secondIsolated j)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
