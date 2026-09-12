import GroupApproximation.GGT.DGOProposition414OppositePartnerCoordinate

/-!
# Canonical local target sets of the balanced-split children

Each gap child inherits the distinguished original sides lying in its open
arc interval.  It also receives precisely those opposite-half chord partners
whose canonical chord-walk occurrence chose that child.  The two classes use
disjoint side blocks of the auxiliary cycle.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The distinguished inherited sides of the first open arc. -/
noncomputable def firstArcTargetSides
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Finset ℕ :=
  B.firstTarget.image B.firstTargetSide

/-- The distinguished inherited sides of the wrapped open arc. -/
noncomputable def secondArcTargetSides
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Finset ℕ :=
  B.secondTarget.image B.secondTargetSide

/-- First-arc targets retained in one open gap. -/
noncomputable def firstGapArcSources
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : Finset ℕ :=
  B.firstTarget.filter fun s =>
    B.firstGapStartSide j ≤ B.firstTargetSide s ∧
      B.firstTargetSide s < B.firstGapFinishSide j

/-- Wrapped-arc targets retained in one open gap. -/
noncomputable def secondGapArcSources
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : Finset ℕ :=
  B.secondTarget.filter fun s =>
    B.secondGapStartSide j ≤ B.secondTargetSide s ∧
      B.secondTargetSide s < B.secondGapFinishSide j

/-- Local auxiliary-cycle indices of inherited first-arc targets. -/
noncomputable def firstGapArcTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : Finset ℕ :=
  (B.firstGapArcSources j).image fun s =>
    (B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j)

/-- Local auxiliary-cycle indices of inherited wrapped-arc targets. -/
noncomputable def secondGapArcTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : Finset ℕ :=
  (B.secondGapArcSources j).image fun s =>
    (B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j)

/-- The canonical wrapped-half child selected for a broken first-half
partner.  Outside the broken set the value is the harmless initial child. -/
noncomputable def firstPartnerSecondGapOwner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) :
    Fin B.brokenAssignment.index.second.pieceCount :=
  if hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives then
    Classical.choose (B.exists_secondGap_containing_firstPartner s hs)
  else ⟨0, by simp [GreedyHalfFamilyIndex.pieceCount]⟩

/-- The canonical first-half child selected for a broken wrapped-half
partner. -/
noncomputable def secondPartnerFirstGapOwner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) :
    Fin B.brokenAssignment.index.first.pieceCount :=
  if hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives then
    Classical.choose (B.exists_firstGap_containing_secondPartner s hs)
  else ⟨0, by simp [GreedyHalfFamilyIndex.pieceCount]⟩

theorem firstPartnerSecondGapOwner_edge
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.firstTarget
      B.componentPlacement.firstSurvives) :
    EdgeBetween
      (B.secondGapChordStart (B.firstPartnerSecondGapOwner s))
      (B.secondGapChordFinish (B.firstPartnerSecondGapOwner s))
      (B.brokenAssignment.first.partner s) := by
  classical
  unfold firstPartnerSecondGapOwner
  rw [dif_pos hs]
  exact Classical.choose_spec
    (B.exists_secondGap_containing_firstPartner s hs)

theorem secondPartnerFirstGapOwner_edge
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (s : ℕ) (hs : s ∈ brokenSet B.componentPlacement.secondTarget
      B.componentPlacement.secondSurvives) :
    EdgeBetween
      (B.firstGapChordStart (B.secondPartnerFirstGapOwner s))
      (B.firstGapChordFinish (B.secondPartnerFirstGapOwner s))
      (B.brokenAssignment.second.partner s) := by
  classical
  unfold secondPartnerFirstGapOwner
  rw [dif_pos hs]
  exact Classical.choose_spec
    (B.exists_firstGap_containing_secondPartner s hs)

/-- Broken wrapped-half sources whose opposite partner is charged in `j`. -/
noncomputable def firstGapChordSources
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : Finset ℕ :=
  (brokenSet B.componentPlacement.secondTarget
    B.componentPlacement.secondSurvives).filter fun s =>
      B.secondPartnerFirstGapOwner s = j

/-- Broken first-half sources whose opposite partner is charged in `j`. -/
noncomputable def secondGapChordSources
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : Finset ℕ :=
  (brokenSet B.componentPlacement.firstTarget
    B.componentPlacement.firstSurvives).filter fun s =>
      B.firstPartnerSecondGapOwner s = j

/-- Chord-side local targets in a first-half child. -/
noncomputable def firstGapChordTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : Finset ℕ :=
  (B.firstGapChordSources j).image fun s =>
    B.firstGapChordTargetIndex j (B.brokenAssignment.second.partner s)

/-- Chord-side local targets in a wrapped-half child. -/
noncomputable def secondGapChordTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : Finset ℕ :=
  (B.secondGapChordSources j).image fun s =>
    B.secondGapChordTargetIndex j (B.brokenAssignment.first.partner s)

/-- Complete geometric local target of a first-half gap, before adding the
canonical connector target. -/
noncomputable def firstGapLocalTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) : Finset ℕ :=
  B.firstGapArcTarget j ∪ B.firstGapChordTarget j

/-- Complete geometric local target of a wrapped-half gap. -/
noncomputable def secondGapLocalTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) : Finset ℕ :=
  B.secondGapArcTarget j ∪ B.secondGapChordTarget j

theorem firstGapLocalTarget_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) :
    ∀ t ∈ B.firstGapLocalTarget j,
      t < (B.firstGapLeft j).length +
        (B.firstGapFinishSide j - B.firstGapStartSide j) +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
  classical
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    have hrange := (Finset.mem_filter.mp hs).2
    omega
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    have hs' := (Finset.mem_filter.mp hs).1
    have hj := (Finset.mem_filter.mp hs).2
    subst j
    exact auxiliaryChordTargetIndex_lt B.chord
      (B.firstGapLeft (B.secondPartnerFirstGapOwner s))
      (B.firstGapRight (B.secondPartnerFirstGapOwner s))
      (B.firstGapFinishSide (B.secondPartnerFirstGapOwner s) -
        B.firstGapStartSide (B.secondPartnerFirstGapOwner s))
      (B.firstGapChordStart_le _) (B.firstGapChordFinish_le _)
      (B.secondPartnerFirstGapOwner_edge s hs')

theorem secondGapLocalTarget_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) :
    ∀ t ∈ B.secondGapLocalTarget j,
      t < (B.secondGapLeft j).length +
        (B.secondGapFinishSide j - B.secondGapStartSide j) +
        (B.secondGapRight j).length +
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by
  classical
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    have hrange := (Finset.mem_filter.mp hs).2
    omega
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    have hs' := (Finset.mem_filter.mp hs).1
    have hj := (Finset.mem_filter.mp hs).2
    subst j
    exact auxiliaryChordTargetIndex_lt B.chord
      (B.secondGapLeft (B.firstPartnerSecondGapOwner s))
      (B.secondGapRight (B.firstPartnerSecondGapOwner s))
      (B.secondGapFinishSide (B.firstPartnerSecondGapOwner s) -
        B.secondGapStartSide (B.firstPartnerSecondGapOwner s))
      (B.secondGapChordStart_le _) (B.secondGapChordFinish_le _)
      (B.firstPartnerSecondGapOwner_edge s hs')

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
