import GroupApproximation.GGT.DGOProposition414GapTargetAssembly

/-!
# Component families for the balanced gap children

The four-path construction in Dahmani--Guirardel--Osin Proposition 4.14
supplies component assertions for inherited arc targets, opposite chord
targets, and the two connector ranges.  This file records those assertions
without the target-vs-all separation step, and then assembles them with an
explicit separation proposition into the exact `FirstGapTargetCertificate`
and `SecondGapTargetCertificate` structures used by the balanced gap
completion.

The separation propositions are strictly smaller than the certificate fields:
they only rule out a connection from a target start to another recorded
component start.  The component fields themselves are supplied by the
four-path dictionaries in `DGOProposition414GapChildTargetComponents`,
`DGOProposition414GapChordComponents`, and
`DGOProposition414GapConnectorTargetComponents`.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-! ## The strictly smaller separation inputs -/

/-- No component start distinct from a first-gap target is connected to it.
This is the target-vs-all separation clause for one child, before the finite
component-file enumeration is applied. -/
def FirstGapTargetSeparation
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Prop :=
  ∀ j : Fin B.brokenAssignment.index.first.pieceCount,
    ∀ s ∈ B.firstGapTarget j,
      ∀ q : ℕ, q ≠ B.firstGapCut j s →
        IsCompStart (B.firstGapLocalLabel j s) (B.firstGapCycle j) q →
          ¬ Connected D.fam (B.firstGapLocalLabel j s)
            (vertex B.firstBase B.chord (B.firstGapChordFinish j))
            (B.firstGapCycle j) (B.firstGapCut j s) q

/-- No component start distinct from a wrapped-gap target is connected to it.
This is the mirror target-vs-all separation clause for one child. -/
def SecondGapTargetSeparation
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Prop :=
  ∀ j : Fin B.brokenAssignment.index.second.pieceCount,
    ∀ s ∈ B.secondGapTarget j,
      ∀ q : ℕ, q ≠ B.secondGapCut j s →
        IsCompStart (B.secondGapLocalLabel j s) (B.secondGapCycle j) q →
          ¬ Connected D.fam (B.secondGapLocalLabel j s)
            (vertex B.firstBase B.chord (B.secondGapChordFinish j))
            (B.secondGapCycle j) (B.secondGapCut j s) q

/-! ## Component-only family records -/

/-- Component assertions for all four target classes in a first-gap child.
The labels and coordinates are exactly those in
`BalancedSplitData.FirstGapTargetCertificate`; no isolation assertion is
duplicated here. -/
structure FirstGapComponentFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  arcComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (s : ℕ), s ∈ B.firstGapArcSources j →
      IsComp (B.firstGapLocalLabel j
          ((B.firstGapLeft j).length +
            (B.firstTargetSide s - B.firstGapStartSide j)))
        (B.firstGapCycle j)
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j) + 1))
  chordComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (s : ℕ), s ∈ B.firstGapChordSources j →
      IsComp (B.firstGapLocalLabel j
          (B.firstGapChordTargetIndex j
            (B.brokenAssignment.second.partner s)))
        (B.firstGapCycle j)
        (B.firstGapCut j (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s)))
        (B.firstGapCut j (B.firstGapChordTargetIndex j
          (B.brokenAssignment.second.partner s) + 1))
  leftComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (r : ℕ), r < (B.firstGapLeft j).length →
      IsComp (B.firstGapLocalLabel j r) (B.firstGapCycle j)
        (B.firstGapCut j r) (B.firstGapCut j (r + 1))
  rightComponent : ∀ (j : Fin B.brokenAssignment.index.first.pieceCount)
      (r : ℕ), r < (B.firstGapRight j).length →
      IsComp (B.firstGapLocalLabel j
          ((B.firstGapLeft j).length +
            (B.firstGapFinishSide j - B.firstGapStartSide j) + r))
        (B.firstGapCycle j)
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + r))
        (B.firstGapCut j ((B.firstGapLeft j).length +
          (B.firstGapFinishSide j - B.firstGapStartSide j) + r + 1))

/-- Component assertions for all four target classes in a wrapped-gap child.
The coordinates agree definitionally with
`BalancedSplitData.SecondGapTargetCertificate`. -/
structure SecondGapComponentFamily
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) where
  arcComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (s : ℕ), s ∈ B.secondGapArcSources j →
      IsComp (B.secondGapLocalLabel j
          ((B.secondGapLeft j).length +
            (B.secondTargetSide s - B.secondGapStartSide j)))
        (B.secondGapCycle j)
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j) + 1))
  chordComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (s : ℕ), s ∈ B.secondGapChordSources j →
      IsComp (B.secondGapLocalLabel j
          (B.secondGapChordTargetIndex j
            (B.brokenAssignment.first.partner s)))
        (B.secondGapCycle j)
        (B.secondGapCut j (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s)))
        (B.secondGapCut j (B.secondGapChordTargetIndex j
          (B.brokenAssignment.first.partner s) + 1))
  leftComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (r : ℕ), r < (B.secondGapLeft j).length →
      IsComp (B.secondGapLocalLabel j r) (B.secondGapCycle j)
        (B.secondGapCut j r) (B.secondGapCut j (r + 1))
  rightComponent : ∀ (j : Fin B.brokenAssignment.index.second.pieceCount)
      (r : ℕ), r < (B.secondGapRight j).length →
      IsComp (B.secondGapLocalLabel j
          ((B.secondGapLeft j).length +
            (B.secondGapFinishSide j - B.secondGapStartSide j) + r))
        (B.secondGapCycle j)
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + r))
        (B.secondGapCut j ((B.secondGapLeft j).length +
          (B.secondGapFinishSide j - B.secondGapStartSide j) + r + 1))

/-! ## Exact certificate assembly -/

/-- Assemble a first-gap component family and its separation input into the
exact certificate consumed by `gapCompletion_of_certificates`. -/
theorem FirstGapComponentFamily.toCertificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (F : FirstGapComponentFamily B)
    (hsep : FirstGapTargetSeparation B) :
    FirstGapTargetCertificate B := by
  refine
    { arcComponent := F.arcComponent
      arcIsolated := ?_
      chordComponent := F.chordComponent
      chordIsolated := ?_
      leftComponent := F.leftComponent
      leftIsolated := ?_
      rightComponent := F.rightComponent
      rightIsolated := ?_ } 
  · intro j s hs
    let q := (B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j)
    have hcomp := F.arcComponent j s hs
    have hstart : IsCompStart (B.firstGapLocalLabel j q)
        (B.firstGapCycle j) (B.firstGapCut j q) := by
      exact ⟨B.firstGapCut j (q + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : q ∈ B.firstGapTarget j := by
      simp only [firstGapTarget, firstGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    exact hsep j q htarget t hne ht hconn
  · intro j s hs
    let q := B.firstGapChordTargetIndex j
      (B.brokenAssignment.second.partner s)
    have hcomp := F.chordComponent j s hs
    have hstart : IsCompStart (B.firstGapLocalLabel j q)
        (B.firstGapCycle j) (B.firstGapCut j q) := by
      exact ⟨B.firstGapCut j (q + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : q ∈ B.firstGapTarget j := by
      simp only [firstGapTarget, firstGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    exact hsep j q htarget t hne ht hconn
  · intro j r hr
    have hcomp := F.leftComponent j r hr
    have hstart : IsCompStart (B.firstGapLocalLabel j r)
        (B.firstGapCycle j) (B.firstGapCut j r) := by
      exact ⟨B.firstGapCut j (r + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : r ∈ B.firstGapTarget j := by
      simp only [firstGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_left
          (B.firstGapLeft j) (B.firstGapRight j)
          (B.firstGapFinishSide j - B.firstGapStartSide j) r hr))
    exact hsep j r htarget t hne ht hconn
  · intro j r hr
    let q := (B.firstGapLeft j).length +
      (B.firstGapFinishSide j - B.firstGapStartSide j) + r
    have hcomp := F.rightComponent j r hr
    have hstart : IsCompStart (B.firstGapLocalLabel j q)
        (B.firstGapCycle j) (B.firstGapCut j q) := by
      exact ⟨B.firstGapCut j (q + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : q ∈ B.firstGapTarget j := by
      simp only [firstGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_right
          (B.firstGapLeft j) (B.firstGapRight j)
          (B.firstGapFinishSide j - B.firstGapStartSide j) r hr))
    exact hsep j q htarget t hne ht hconn

/-- Assemble a wrapped-gap component family and its separation input into the
exact certificate consumed by `gapCompletion_of_certificates`. -/
theorem SecondGapComponentFamily.toCertificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (F : SecondGapComponentFamily B)
    (hsep : SecondGapTargetSeparation B) :
    SecondGapTargetCertificate B := by
  refine
    { arcComponent := F.arcComponent
      arcIsolated := ?_
      chordComponent := F.chordComponent
      chordIsolated := ?_
      leftComponent := F.leftComponent
      leftIsolated := ?_
      rightComponent := F.rightComponent
      rightIsolated := ?_ }
  · intro j s hs
    let q := (B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j)
    have hcomp := F.arcComponent j s hs
    have hstart : IsCompStart (B.secondGapLocalLabel j q)
        (B.secondGapCycle j) (B.secondGapCut j q) := by
      exact ⟨B.secondGapCut j (q + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : q ∈ B.secondGapTarget j := by
      simp only [secondGapTarget, secondGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    exact hsep j q htarget t hne ht hconn
  · intro j s hs
    let q := B.secondGapChordTargetIndex j
      (B.brokenAssignment.first.partner s)
    have hcomp := F.chordComponent j s hs
    have hstart : IsCompStart (B.secondGapLocalLabel j q)
        (B.secondGapCycle j) (B.secondGapCut j q) := by
      exact ⟨B.secondGapCut j (q + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : q ∈ B.secondGapTarget j := by
      simp only [secondGapTarget, secondGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    exact hsep j q htarget t hne ht hconn
  · intro j r hr
    have hcomp := F.leftComponent j r hr
    have hstart : IsCompStart (B.secondGapLocalLabel j r)
        (B.secondGapCycle j) (B.secondGapCut j r) := by
      exact ⟨B.secondGapCut j (r + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : r ∈ B.secondGapTarget j := by
      simp only [secondGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_left
          (B.secondGapLeft j) (B.secondGapRight j)
          (B.secondGapFinishSide j - B.secondGapStartSide j) r hr))
    exact hsep j r htarget t hne ht hconn
  · intro j r hr
    let q := (B.secondGapLeft j).length +
      (B.secondGapFinishSide j - B.secondGapStartSide j) + r
    have hcomp := F.rightComponent j r hr
    have hstart : IsCompStart (B.secondGapLocalLabel j q)
        (B.secondGapCycle j) (B.secondGapCut j q) := by
      exact ⟨B.secondGapCut j (q + 1), hcomp⟩
    refine ⟨hstart, ?_⟩
    intro t hne ht hconn
    have htarget : q ∈ B.secondGapTarget j := by
      simp only [secondGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_right
          (B.secondGapLeft j) (B.secondGapRight j)
          (B.secondGapFinishSide j - B.secondGapStartSide j) r hr))
    exact hsep j q htarget t hne ht hconn

/-- A producer for the two smaller component-family records and their
separation propositions is exactly a producer for the two dgo target
certificates. -/
theorem exists_gapTargetCertificates_of_componentFamilies
    {D : RelGenSet G Λ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (produce : ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
      Nonempty (FirstGapComponentFamily B) ∧
      Nonempty (SecondGapComponentFamily B) ∧
      FirstGapTargetSeparation B ∧ SecondGapTargetSeparation B) :
    ∀ {n k R : ℕ} (P : SumBoundInput D (b : ℝ) n)
      (B : BalancedSplitData D hsymm b hδ P k R),
      Nonempty (FirstGapTargetCertificate B) ∧
      Nonempty (SecondGapTargetCertificate B) := by
  intro n k R P B
  obtain ⟨first, second, hfirstSep, hsecondSep⟩ := produce P B
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨⟨first.toCertificate hfirstSep⟩,
    ⟨second.toCertificate hsecondSep⟩⟩

/-! ## Model tests for the smaller propositions -/

/-- Empty target sets satisfy first-gap separation by vacuity. -/
theorem firstGapTargetSeparation_of_empty
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hempty : ∀ j, B.firstGapTarget j = ∅) :
    FirstGapTargetSeparation B := by
  intro j s hs
  simp [hempty j] at hs

/-- Empty target sets satisfy wrapped-gap separation by vacuity. -/
theorem secondGapTargetSeparation_of_empty
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hempty : ∀ j, B.secondGapTarget j = ∅) :
    SecondGapTargetSeparation B := by
  intro j s hs
  simp [hempty j] at hs

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
