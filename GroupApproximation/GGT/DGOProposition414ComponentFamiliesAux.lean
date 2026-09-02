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

/-! ## Packaging the all-target component family -/

/-- Package an all-target component family into the four first-gap component
fields.  The target memberships are proved by the canonical decomposition of
`firstGapTarget` into arc, chord, and connector blocks. -/
theorem FirstGapComponentFamily.ofTargetComponents
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (htarget : ∀ j, ∀ s ∈ B.firstGapTarget j,
      IsComp (B.firstGapLocalLabel j s) (B.firstGapCycle j)
        (B.firstGapCut j s) (B.firstGapCut j (s + 1))) :
    FirstGapComponentFamily B := by
  refine
    { arcComponent := ?_
      chordComponent := ?_
      leftComponent := ?_
      rightComponent := ?_ }
  · intro j s hs
    let q := (B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j)
    have hq : q ∈ B.firstGapTarget j := by
      simp only [firstGapTarget, firstGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    simpa only [q] using htarget j q hq
  · intro j s hs
    let q := B.firstGapChordTargetIndex j
      (B.brokenAssignment.second.partner s)
    have hq : q ∈ B.firstGapTarget j := by
      simp only [firstGapTarget, firstGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    simpa only [q] using htarget j q hq
  · intro j r hr
    have hq : r ∈ B.firstGapTarget j := by
      simp only [firstGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_left
          (B.firstGapLeft j) (B.firstGapRight j)
          (B.firstGapFinishSide j - B.firstGapStartSide j) r hr))
    exact htarget j r hq
  · intro j r hr
    let q := (B.firstGapLeft j).length +
      (B.firstGapFinishSide j - B.firstGapStartSide j) + r
    have hq : q ∈ B.firstGapTarget j := by
      simp only [firstGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_right
          (B.firstGapLeft j) (B.firstGapRight j)
          (B.firstGapFinishSide j - B.firstGapStartSide j) r hr))
    simpa only [q] using htarget j q hq

/-- Package an all-target component family into the four wrapped-gap
component fields. -/
theorem SecondGapComponentFamily.ofTargetComponents
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    (htarget : ∀ j, ∀ s ∈ B.secondGapTarget j,
      IsComp (B.secondGapLocalLabel j s) (B.secondGapCycle j)
        (B.secondGapCut j s) (B.secondGapCut j (s + 1))) :
    SecondGapComponentFamily B := by
  refine
    { arcComponent := ?_
      chordComponent := ?_
      leftComponent := ?_
      rightComponent := ?_ }
  · intro j s hs
    let q := (B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j)
    have hq : q ∈ B.secondGapTarget j := by
      simp only [secondGapTarget, secondGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    simpa only [q] using htarget j q hq
  · intro j s hs
    let q := B.secondGapChordTargetIndex j
      (B.brokenAssignment.first.partner s)
    have hq : q ∈ B.secondGapTarget j := by
      simp only [secondGapTarget, secondGapLocalTarget]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr ⟨s, hs, rfl⟩))))
    simpa only [q] using htarget j q hq
  · intro j r hr
    have hq : r ∈ B.secondGapTarget j := by
      simp only [secondGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_left
          (B.secondGapLeft j) (B.secondGapRight j)
          (B.secondGapFinishSide j - B.secondGapStartSide j) r hr))
    exact htarget j r hq
  · intro j r hr
    let q := (B.secondGapLeft j).length +
      (B.secondGapFinishSide j - B.secondGapStartSide j) + r
    have hq : q ∈ B.secondGapTarget j := by
      simp only [secondGapTarget]
      exact Finset.mem_union.mpr (Or.inr
        (mem_auxiliaryCycleConnectorTarget_right
          (B.secondGapLeft j) (B.secondGapRight j)
          (B.secondGapFinishSide j - B.secondGapStartSide j) r hr))
    simpa only [q] using htarget j q hq

/-
/-! ## The inherited-arc seam -/

/-- An inherited first-gap target remains a component of the complete
auxiliary cycle.  Interior targets transfer by geodesic restriction.  At a
gap endpoint, the preceding or following broken component supplies the
maximality letter, while a surviving half supplies the terminal exclusion;
these are the endpoint cases in DGO Proposition 4.14. -/
theorem firstGapArcSource_fullComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    IsComp (B.firstGapLocalLabel j
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1)) := by
  have hsData := Finset.mem_filter.mp hs
  let i := B.firstArcCut (B.firstTargetSide s) -
    B.firstArcCut (B.firstGapStartSide j)
  let cycle := auxiliaryCycleWord (B.firstGapLeft j)
    (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
      (B.firstGapFinishSide j)) (B.firstGapRight j)
    (orientedSegment B.chord (B.firstGapChordStart j)
      (B.firstGapChordFinish j))
  have hcycleLen : cycle.length =
      (B.firstGapLeft j).length +
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length +
        (B.firstGapRight j).length +
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)).length := by
    simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord,
      Nat.add_assoc]
  have hlocalComp : IsComp (P.label s)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j)) i (i + 1) := by
    simpa only [i] using B.firstGapArcSource_component j s hs
  have hstart : ∀ t : ℕ,
      (B.firstGapLeft j).length + i = t + 1 →
      ∀ ht : t < cycle.length, ¬ (cycle[t]'ht).IsCompOf (P.label s) := by
    intro t hteq ht hcycleComp
    by_cases hi : 0 < i
    · have hteq' : (B.firstGapLeft j).length + (i - 1) = t := by
        dsimp [i] at hteq ⊢
        omega
      have htArc : i - 1 <
          (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
            (B.firstGapFinishSide j)).length := by
        have hlocalLen := hlocalComp.2.1
        omega
      have hrCycle : (B.firstGapLeft j).length + (i - 1) < cycle.length := by
        rw [hteq']
        exact ht
      have hcycleLetter := hcycleComp
      change ((auxiliaryCycleWord (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)))[t]'ht).IsCompOf (P.label s) at hcycleLetter
      have hletter := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
        (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)) (i - 1)
        htArc hrCycle).mp (by
          change ((auxiliaryCycleWord (B.firstGapLeft j)
            (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
              (B.firstGapFinishSide j)) (B.firstGapRight j)
            (orientedSegment B.chord (B.firstGapChordStart j)
              (B.firstGapChordFinish j)))[
                (B.firstGapLeft j).length + (i - 1)]'hrCycle).IsCompOf
            (P.label s)
          simpa only [hteq'] using hcycleLetter)
      exact hlocalComp.2.2.2.1 (i - 1) (by omega) (by omega) hletter
    · have hi0 : i = 0 := by omega
      have hdiff0 : B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j) = 0 := by
        simpa only [i] using hi0
      subst i
      by_cases hp : HalfGap.previousEntry B.brokenAssignment.index.first j = none
      · have hleft0 : (B.firstGapLeft j).length = 0 := by
          classical
          simp only [firstGapLeft]
          rw [hp]
          simp
        omega
      · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hp
        have heq : HalfGap.previousEntry B.brokenAssignment.index.first j = some e := by
          simpa using he
        have htleft : t < (B.firstGapLeft j).length := by omega
        have hconn := B.firstGap_leftConnector_isCompOf j e heq t htleft (by
          simp only [cycle] at ht
          simpa [auxiliaryCycleWord, OsinComponents.length_revWord] using ht)
        have hconnLabel := B.firstGapLocalLabel_leftConnector j e heq t htleft
        have hconn' :
            (cycle[t]'ht).IsCompOf
              (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
          rw [← hconnLabel]
          exact hconn
        have hEqLabel : P.label s =
            P.label (HalfEntry.entrySource B.brokenAssignment.index.first e) :=
          eq_of_isCompOf_of_isCompOf hcycleComp hconn'
        have heSrc := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
        have heTarget := (mem_brokenSet_iff.mp heSrc).1
        have hprevComp := B.firstArc_targetComponent heTarget
        have hprevSide : B.firstGapStartSide j =
            B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e) + 1 := by
          simp only [firstGapStartSide]
          rw [heq]
        have hprevPos : B.firstArcCut
            (B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e)) + 1 =
            B.firstArcCut (B.firstGapStartSide j) := by
          calc
            B.firstArcCut (B.firstTargetSide
                (HalfEntry.entrySource B.brokenAssignment.index.first e)) + 1 =
                B.firstTargetPos (HalfEntry.entrySource
                  B.brokenAssignment.index.first e) + 1 := by
              rw [(B.firstArcCut_target heTarget).1]
            _ = B.firstArcCut (B.firstTargetSide
                (HalfEntry.entrySource B.brokenAssignment.index.first e) + 1) :=
              (B.firstArcCut_target heTarget).2.symm
            _ = B.firstArcCut (B.firstGapStartSide j) := by rw [hprevSide]
        have hprevCutLt : B.firstArcCut (B.firstTargetSide
            (HalfEntry.entrySource B.brokenAssignment.index.first e)) <
            B.firstArc.length := by
          rw [(B.firstArcCut_target heTarget).1]
          have hcompLen := hprevComp.2.1
          omega
        have hprevLetter :
            (B.firstArc[B.firstArcCut (B.firstTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.first e))]'(by
                exact hprevCutLt)).IsCompOf
              (P.label (HalfEntry.entrySource
                B.brokenAssignment.index.first e)) := by
          have hposLt : B.firstTargetPos
              (HalfEntry.entrySource B.brokenAssignment.index.first e) <
              B.firstArc.length := by
            have hcompLen := hprevComp.2.1
            omega
          have hletter0 := hprevComp.2.2.1
            (B.firstTargetPos (HalfEntry.entrySource
              B.brokenAssignment.index.first e)) le_rfl (by omega) hposLt
          rw [getElem_congr_idx (B.firstArcCut_target heTarget).1]
          exact hletter0
        have hprevLabel :
            (B.firstArc[B.firstArcCut (B.firstTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.first e))]'(by
                exact hprevCutLt)).IsCompOf (P.label s) := by
          simpa only [hEqLabel] using hprevLetter
        have hparent := B.firstArc_targetComponent hsData.1
        have hidx : B.firstArcCut (B.firstTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.first e)) =
            B.firstArcCut (B.firstTargetSide s) - 1 := by
          have hcur : B.firstArcCut (B.firstTargetSide s) =
              B.firstArcCut (B.firstGapStartSide j) := by
            have hcuts : B.firstArcCut (B.firstTargetSide s) =
                B.firstArcCut (B.firstGapStartSide j) := by
              apply Nat.le_antisymm
              · exact Nat.sub_eq_zero_iff_le.mp hdiff0
              · exact B.firstArc_isCutPath.cut.mono_le hsData.2.1
            exact (B.firstArcCut_target hsData.1).1.trans hcuts
          rw [hcur, ← hprevPos]
          omega
        apply hparent.2.2.2.1
          (B.firstArcCut (B.firstTargetSide s) - 1) (by omega) _ hprevLabel
  have hend : ∀ hn :
      (B.firstGapLeft j).length + i + 1 < cycle.length,
      ¬ (cycle[(B.firstGapLeft j).length + i + 1]'hn).IsCompOf (P.label s) := by
    intro hn hletter
    by_cases hiend : i + 1 <
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length
    · have hco := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
        (B.firstGapLeft j)
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)) (B.firstGapRight j)
        (orientedSegment B.chord (B.firstGapChordStart j)
          (B.firstGapChordFinish j)) (i + 1) hiend
          (by simpa only [cycle, Nat.add_assoc] using hn)).mp (by
            simpa only [cycle, Nat.add_assoc] using hletter)
      exact hlocalComp.2.2.2.2 (by omega) hco
    · have hiEq : i + 1 =
        (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
          (B.firstGapFinishSide j)).length := by
        have hcutEnd := B.firstArc_isCutPath.cut.le_length
          (B.firstGapFinishSide_le j)
        have hlenArc := length_arcWord B.firstArc B.firstArcCut hcutEnd
        rw [hlenArc]
        dsimp [i]
        omega
      by_cases hnxt : HalfGap.nextEntry B.brokenAssignment.index.first j = none
      · have hsurv := B.firstGapArcSource_survives j s hs
        have hwordComp := hsurv.1
        have hwordPost := hwordComp.2.2.2.2
        have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
          rw [show B.refinedCut (B.secondSide + 2) = B.secondVertex by
            simp [BalancedSplitData.refinedCut, splitPairCut_right]]
          exact B.secondVertex_mem.2.trans
            (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
        have hArcLen : B.firstArc.length = B.firstArcLength := by
          change (arcWord P.word B.refinedCut (B.firstSide + 1)
            (B.secondSide + 2)).length = B.firstArcLength
          rw [length_arcWord P.word B.refinedCut hEnd]
          simp [firstArcLength, refinedCut,
            splitPairCut_left B.side_order, splitPairCut_right]
        have hwordLength : B.firstWord.length =
            B.firstArcLength + B.chord.length := by
          rw [BalancedSplitData.firstWord,
            length_firstHalf P.word B.refinedCut hEnd]
          rw [show B.refinedCut (B.firstSide + 1) = B.firstVertex by
            simp [BalancedSplitData.refinedCut,
              splitPairCut_left B.side_order],
            show B.refinedCut (B.secondSide + 2) = B.secondVertex by
            simp [BalancedSplitData.refinedCut, splitPairCut_right]]
          rfl
        have hwordLen : B.firstWord.length =
            B.firstArc.length + B.chord.length := by
          rw [hArcLen]
          exact hwordLength
        have htargetLt : B.firstTargetPos s + 1 < B.firstWord.length := by
          rw [hwordLen]
          have hparentEnd := (B.firstArc_targetComponent hsData.1).2.1
          have hsegLen := length_arcWord B.firstArc B.firstArcCut
            (B.firstArc_isCutPath.cut.le_length (B.firstGapFinishSide_le j))
          have hchordPos : 0 < B.chord.length := by
            have hn' := hn
            rw [hcycleLen] at hn'
            have hrightNil : B.firstGapRight j = [] := by
              simp only [firstGapRight]
              rw [hnxt]
            simp only [hrightNil, List.length_nil, Nat.add_zero] at hn'
            rw [hsegLen] at hiEq
            omega
          omega
        have hauxEq : (cycle[(B.firstGapLeft j).length + i + 1]'hn) =
            B.firstWord[B.firstTargetPos s + 1]'(by
              exact htargetLt) := by
          have hcutCur := (B.firstArcCut_target hsData.1).1
          have hcutNext := (B.firstArcCut_target hsData.1).2
          have hrightNil : B.firstGapRight j = [] := by
            simp only [firstGapRight]
            rw [hnxt]
          simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord,
            hwordComp, hwordLen, hArcLen, hiEq, hcutCur, hcutNext, hrightNil]
          omega
        rw [hauxEq] at hletter
        exact hwordPost (by omega) hletter
      · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hnxt
        have heq : HalfGap.nextEntry B.brokenAssignment.index.first j = some e := by
          simpa using he
        have heSrc := HalfEntry.entrySource_mem B.brokenAssignment.index.first e
        have heTarget := (mem_brokenSet_iff.mp heSrc).1
        have hright : B.firstGapFinishSide j =
            B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e) := by
          simp only [firstGapFinishSide]
          rw [heq]
        have hrightPos : 0 < (B.firstGapRight j).length := by
          have := B.firstGapRight_length_le_one j
          omega
        have hnextComp := B.firstGap_rightConnector_isCompOf j e heq 0 (by
          exact hrightPos) (by
            simpa [cycle, auxiliaryCycleWord, OsinComponents.length_revWord] using hn)
        have hnextLabel := B.firstGapLocalLabel_rightConnector j e heq 0 hrightPos
        have hnextComp' :
            (cycle[(B.firstGapLeft j).length + i + 1]'hn).IsCompOf
              (P.label (HalfEntry.entrySource B.brokenAssignment.index.first e)) := by
          rw [← hnextLabel] at hnextComp
          simpa only [Nat.add_zero] using hnextComp
        have hnextEq : P.label s = P.label
            (HalfEntry.entrySource B.brokenAssignment.index.first e) :=
          eq_of_isCompOf_of_isCompOf hletter hnextComp'
        have hparent := B.firstArc_targetComponent hsData.1
        have hnextLetter : (B.firstArc[B.firstArcCut
            (B.firstTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.first e))]'(by
                exact B.firstArc_isCutPath.cut.le_length
                  (B.firstTargetSide_lt heTarget).le)).IsCompOf (P.label s) := by
          have hh := hparent.2.2.1 _ le_rfl (by omega) _
          simpa only [hnextEq] using hh
        exact hlocalComp.2.2.2.2 _ (by omega) (by omega) hnextLetter
  have hraw := firstGapArcSource_cycleComponent_of_boundary B j s hstart hend
  have harc : IsPolygonCut
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) :=
    isPolygonCut_arcWord B.firstArc_isCutPath.cut
      (B.firstGap_side_order j) (B.firstGapFinishSide_le j)
  have hcut0 := auxiliaryCycleCut_arc (B.firstGapLeft j)
    (B.firstGapRight j) harc
    (r := B.firstTargetSide s - B.firstGapStartSide j) (by
      have hs' := hsData.2
      omega)
  have harg0 : B.firstGapStartSide j +
      (B.firstTargetSide s - B.firstGapStartSide j) =
      B.firstTargetSide s := by omega
  rw [harg0] at hcut0
  have hcut1 : B.firstGapCut j
      ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length + i + 1 := by
    have hr : B.firstTargetSide s - B.firstGapStartSide j + 1 ≤
        B.firstGapFinishSide j - B.firstGapStartSide j := by
      omega
    have h := auxiliaryCycleCut_arc (B.firstGapLeft j)
      (B.firstGapRight j) harc
      (r := B.firstTargetSide s - B.firstGapStartSide j + 1) hr
    have hcutTarget := (B.firstArcCut_target hsData.1).2
    dsimp [firstGapCut, i]
    rw [h]
    have harg : B.firstGapStartSide j +
        (B.firstTargetSide s - B.firstGapStartSide j + 1) =
        B.firstTargetSide s + 1 := by omega
    rw [harg, hcutTarget]
    omega
  dsimp [firstGapCycle, firstGapCut]
  rw [hcut0]
  have hcut1' : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
      ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length + i + 1 := by
    convert hcut1 using 1 <;> omega
  rw [hcut1'] at ⊢
  simpa only [cycle, B.firstGapLocalLabel_arc j s hs, Nat.add_assoc] using hraw

/-! ## The wrapped inherited-arc seam -/

/-- The wrapped inherited target remains a component of the complete
auxiliary cycle.  The proof is the reflected endpoint argument from DGO
Proposition 4.14: interior positions use arc restriction, while a boundary
position is excluded by the adjacent connector or by the surviving half. -/
theorem secondGapArcSource_fullComponent
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    IsComp (B.secondGapLocalLabel j
        ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1)) := by
  have hsData := Finset.mem_filter.mp hs
  let i := B.secondArcCut (B.secondTargetSide s) -
    B.secondArcCut (B.secondGapStartSide j)
  let cycle := auxiliaryCycleWord (B.secondGapLeft j)
    (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
      (B.secondGapFinishSide j)) (B.secondGapRight j)
    (orientedSegment B.chord (B.secondGapChordStart j)
      (B.secondGapChordFinish j))
  have hcycleLen : cycle.length =
      (B.secondGapLeft j).length +
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length +
        (B.secondGapRight j).length +
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)).length := by
    simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord,
      Nat.add_assoc]
  have hlocalComp : IsComp (P.label s)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j)) i (i + 1) := by
    simpa only [i] using B.secondGapArcSource_component j s hs
  have hstart : ∀ t : ℕ,
      (B.secondGapLeft j).length + i = t + 1 →
      ∀ ht : t < cycle.length, ¬ (cycle[t]'ht).IsCompOf (P.label s) := by
    intro t hteq ht hcycleComp
    by_cases hi : 0 < i
    · have hteq' : (B.secondGapLeft j).length + (i - 1) = t := by
        dsimp [i] at hteq ⊢
        omega
      have htArc : i - 1 <
          (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
            (B.secondGapFinishSide j)).length := by
        have hlocalLen := hlocalComp.2.1
        omega
      have hrCycle : (B.secondGapLeft j).length + (i - 1) < cycle.length := by
        rw [hteq']
        exact ht
      have hcycleLetter := hcycleComp
      change ((auxiliaryCycleWord (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)) (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)))[t]'ht).IsCompOf (P.label s) at hcycleLetter
      have hletter := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
        (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)) (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)) (i - 1)
        htArc hrCycle).mp (by
          change ((auxiliaryCycleWord (B.secondGapLeft j)
            (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
              (B.secondGapFinishSide j)) (B.secondGapRight j)
            (orientedSegment B.chord (B.secondGapChordStart j)
              (B.secondGapChordFinish j)))[
                (B.secondGapLeft j).length + (i - 1)]'hrCycle).IsCompOf
            (P.label s)
          simpa only [hteq'] using hcycleLetter)
      exact hlocalComp.2.2.2.1 (i - 1) (by omega) (by omega) hletter
    · have hi0 : i = 0 := by omega
      have hdiff0 : B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j) = 0 := by
        simpa only [i] using hi0
      subst i
      by_cases hp : HalfGap.previousEntry B.brokenAssignment.index.second j = none
      · have hleft0 : (B.secondGapLeft j).length = 0 := by
          classical
          simp only [secondGapLeft]
          rw [hp]
          simp
        omega
      · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hp
        have heq : HalfGap.previousEntry B.brokenAssignment.index.second j = some e := by
          simpa using he
        have htleft : t < (B.secondGapLeft j).length := by omega
        have hconn := B.secondGap_leftConnector_isCompOf j e heq t htleft (by
          simp only [cycle] at ht
          simpa [auxiliaryCycleWord, OsinComponents.length_revWord] using ht)
        have hconnLabel := B.secondGapLocalLabel_leftConnector j e heq t htleft
        have hconn' :
            (cycle[t]'ht).IsCompOf
              (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
          rw [← hconnLabel]
          exact hconn
        have hEqLabel : P.label s =
            P.label (HalfEntry.entrySource B.brokenAssignment.index.second e) :=
          eq_of_isCompOf_of_isCompOf hcycleComp hconn'
        have heSrc := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
        have heTarget := (mem_brokenSet_iff.mp heSrc).1
        have hprevComp := B.secondArc_targetComponent heTarget
        have hprevSide : B.secondGapStartSide j =
            B.secondTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.second e) + 1 := by
          simp only [secondGapStartSide]
          rw [heq]
        have hprevPos : B.secondArcCut
            (B.secondTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.second e)) + 1 =
            B.secondArcCut (B.secondGapStartSide j) := by
          calc
            B.secondArcCut (B.secondTargetSide
                (HalfEntry.entrySource B.brokenAssignment.index.second e)) + 1 =
                B.secondTargetPos (HalfEntry.entrySource
                  B.brokenAssignment.index.second e) + 1 := by
              rw [(B.secondArcCut_target heTarget).1]
            _ = B.secondArcCut (B.secondTargetSide
                (HalfEntry.entrySource B.brokenAssignment.index.second e) + 1) :=
              (B.secondArcCut_target heTarget).2.symm
            _ = B.secondArcCut (B.secondGapStartSide j) := by rw [hprevSide]
        have hprevCutLt : B.secondArcCut (B.secondTargetSide
            (HalfEntry.entrySource B.brokenAssignment.index.second e)) <
            B.secondArc.length := by
          rw [(B.secondArcCut_target heTarget).1]
          have hcompLen := hprevComp.2.1
          omega
        have hprevLetter :
            (B.secondArc[B.secondArcCut (B.secondTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.second e))]'(by
                exact hprevCutLt)).IsCompOf
              (P.label (HalfEntry.entrySource
                B.brokenAssignment.index.second e)) := by
          have hposLt : B.secondTargetPos
              (HalfEntry.entrySource B.brokenAssignment.index.second e) <
              B.secondArc.length := by
            have hcompLen := hprevComp.2.1
            omega
          have hletter0 := hprevComp.2.2.1
            (B.secondTargetPos (HalfEntry.entrySource
              B.brokenAssignment.index.second e)) le_rfl (by omega) hposLt
          rw [getElem_congr_idx (B.secondArcCut_target heTarget).1]
          exact hletter0
        have hprevLabel :
            (B.secondArc[B.secondArcCut (B.secondTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.second e))]'(by
                exact hprevCutLt)).IsCompOf (P.label s) := by
          simpa only [hEqLabel] using hprevLetter
        have hparent := B.secondArc_targetComponent hsData.1
        have hidx : B.secondArcCut (B.secondTargetSide
              (HalfEntry.entrySource B.brokenAssignment.index.second e)) =
            B.secondArcCut (B.secondTargetSide s) - 1 := by
          have hcur : B.secondArcCut (B.secondTargetSide s) =
              B.secondArcCut (B.secondGapStartSide j) := by
            have hcuts : B.secondArcCut (B.secondTargetSide s) =
                B.secondArcCut (B.secondGapStartSide j) := by
              apply Nat.le_antisymm
              · exact Nat.sub_eq_zero_iff_le.mp hdiff0
              · exact B.secondArc_isCutPath.cut.mono_le hsData.2.1
            exact (B.secondArcCut_target hsData.1).1.trans hcuts
          rw [hcur, ← hprevPos]
          omega
        apply hparent.2.2.2.1
          (B.secondArcCut (B.secondTargetSide s) - 1) (by omega) _ hprevLabel
  have hend : ∀ hn :
      (B.secondGapLeft j).length + i + 1 < cycle.length,
      ¬ (cycle[(B.secondGapLeft j).length + i + 1]'hn).IsCompOf (P.label s) := by
    intro hn hletter
    by_cases hiend : i + 1 <
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length
    · have hco := (isCompOf_auxiliaryCycle_arc_iff (P.label s)
        (B.secondGapLeft j)
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)) (B.secondGapRight j)
        (orientedSegment B.chord (B.secondGapChordStart j)
          (B.secondGapChordFinish j)) (i + 1) hiend
          (by simpa only [cycle, Nat.add_assoc] using hn)).mp (by
            simpa only [cycle, Nat.add_assoc] using hletter)
      exact hlocalComp.2.2.2.2 (by omega) hco
    · have hiEq : i + 1 =
        (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
          (B.secondGapFinishSide j)).length := by
        have hlenArc := length_arcWord B.secondArc B.secondArcCut
          (B.secondGapFinishSide_le j)
        rw [hlenArc]
        dsimp [i]
        omega
      by_cases hnxt : HalfGap.nextEntry B.brokenAssignment.index.second j = none
      · have hsurv := B.secondGapArcSource_survives j s hs
        have hwordComp := hsurv.1
        have hwordPost := hwordComp.2.2.2.2
        have hArcLen : B.secondArc.length = B.secondArcLength := by
          rw [secondArc, List.length_append, List.length_drop, List.length_take]
          simp only [secondArcLength]
          omega
        have hwordLength : B.secondWord.length =
            B.secondArcLength + B.chord.length := by
          rw [BalancedSplitData.secondWord,
            length_secondHalf P.word B.refinedCut]
          · rw [show B.refinedCut (B.secondSide + 2) = B.secondVertex by
              simp [BalancedSplitData.refinedCut, splitPairCut_right],
              show B.refinedCut (B.firstSide + 1) = B.firstVertex by
              simp [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]]
            rfl
          · rw [BalancedSplitData.refinedCut, splitPairCut_left B.side_order]
            exact B.firstVertex_mem.2.trans
              (P.polygonCut.le_length
                ((Nat.succ_le_iff.mpr B.side_order).trans
                  (le_of_lt B.secondSide_lt)))
        have hwordLen : B.secondWord.length =
            B.secondArc.length + B.chord.length := by
          rw [hArcLen]
          exact hwordLength
        have htargetLt : B.secondTargetPos s + 1 < B.secondWord.length := by
          rw [hwordLen]
          have hparentEnd := (B.secondArc_targetComponent hsData.1).2.1
          have hsegLen := length_arcWord B.secondArc B.secondArcCut
            (B.secondArc_isCutPath.cut.le_length (B.secondGapFinishSide_le j))
          have hchordPos : 0 < B.chord.length := by
            have hn' := hn
            rw [hcycleLen] at hn'
            have hrightNil : B.secondGapRight j = [] := by
              simp only [secondGapRight]
              rw [hnxt]
            simp only [hrightNil, List.length_nil, Nat.add_zero] at hn'
            rw [hsegLen] at hiEq
            omega
          omega
        have hauxEq : (cycle[(B.secondGapLeft j).length + i + 1]'hn) =
            B.secondWord[B.secondTargetPos s + 1]'(by
              exact htargetLt) := by
          have hcutCur := (B.secondArcCut_target hsData.1).1
          have hcutNext := (B.secondArcCut_target hsData.1).2
          have hrightNil : B.secondGapRight j = [] := by
            simp only [secondGapRight]
            rw [hnxt]
          simp [cycle, auxiliaryCycleWord, OsinComponents.length_revWord,
            hwordComp, hwordLen, hArcLen, hiEq, hcutCur, hcutNext, hrightNil]
          omega
        rw [hauxEq] at hletter
        exact hwordPost (by omega) hletter
      · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hnxt
        have heq : HalfGap.nextEntry B.brokenAssignment.index.second j = some e := by
          simpa using he
        have heSrc := HalfEntry.entrySource_mem B.brokenAssignment.index.second e
        have heTarget := (mem_brokenSet_iff.mp heSrc).1
        have hright : B.secondGapFinishSide j =
            B.secondTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.second e) := by
          simp only [secondGapFinishSide]
          rw [heq]
        have hrightPos : 0 < (B.secondGapRight j).length := by
          have := B.secondGapRight_length_le_one j
          omega
        have hnextComp := B.secondGap_rightConnector_isCompOf j e heq 0 (by
          exact hrightPos) (by
            simpa [cycle, auxiliaryCycleWord, OsinComponents.length_revWord] using hn)
        have hnextLabel := B.secondGapLocalLabel_rightConnector j e heq 0 hrightPos
        have hnextComp' :
            (cycle[(B.secondGapLeft j).length + i + 1]'hn).IsCompOf
              (P.label (HalfEntry.entrySource B.brokenAssignment.index.second e)) := by
          rw [← hnextLabel] at hnextComp
          simpa only [Nat.add_zero] using hnextComp
        have hnextEq : P.label s = P.label
            (HalfEntry.entrySource B.brokenAssignment.index.second e) :=
          eq_of_isCompOf_of_isCompOf hletter hnextComp'
        have hparent := B.secondArc_targetComponent hsData.1
        have hnextLetter : (B.secondArc[B.secondArcCut
            (B.secondTargetSide (HalfEntry.entrySource
              B.brokenAssignment.index.second e))]'(by
                exact B.secondArc_isCutPath.cut.le_length
                  (B.secondTargetSide_lt heTarget).le)).IsCompOf (P.label s) := by
          have hh := hparent.2.2.1 _ le_rfl (by omega) _
          simpa only [hnextEq] using hh
        exact hlocalComp.2.2.2.2 _ (by omega) (by omega) hnextLetter
  have hraw := secondGapArcSource_cycleComponent_of_boundary B j s hstart hend
  have harc : IsPolygonCut
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) :=
    isPolygonCut_arcWord B.secondArc_isCutPath.cut
      (B.secondGap_side_order j) (B.secondGapFinishSide_le j)
  have hcut0 := auxiliaryCycleCut_arc (B.secondGapLeft j)
    (B.secondGapRight j) harc
    (r := B.secondTargetSide s - B.secondGapStartSide j) (by
      have hs' := hsData.2
      omega)
  have harg0 : B.secondGapStartSide j +
      (B.secondTargetSide s - B.secondGapStartSide j) =
      B.secondTargetSide s := by omega
  rw [harg0] at hcut0
  have hcut1 : B.secondGapCut j
      ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length + i + 1 := by
    have hr : B.secondTargetSide s - B.secondGapStartSide j + 1 ≤
        B.secondGapFinishSide j - B.secondGapStartSide j := by omega
    have h := auxiliaryCycleCut_arc (B.secondGapLeft j)
      (B.secondGapRight j) harc
      (r := B.secondTargetSide s - B.secondGapStartSide j + 1) hr
    have hcutTarget := (B.secondArcCut_target hsData.1).2
    dsimp [secondGapCut, i]
    rw [h]
    have harg : B.secondGapStartSide j +
        (B.secondTargetSide s - B.secondGapStartSide j + 1) =
        B.secondTargetSide s + 1 := by omega
    rw [harg, hcutTarget]
    omega
  dsimp [secondGapCycle, secondGapCut]
  rw [hcut0]
  have hcut1' : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j)
      ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length + i + 1 := by
    convert hcut1 using 1 <;> omega
  rw [hcut1'] at ⊢
  simpa only [cycle, B.secondGapLocalLabel_arc j s hs, Nat.add_assoc] using hraw
-/

/-! ## Conditional endpoint bridges -/

/-- The two endpoint exclusions required to extend an inherited arc component
across the first-gap auxiliary cycle.  This is strictly smaller than the
component assertion: it only controls the two neighbouring letters. -/
def FirstGapArcBoundaryExclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) : Prop :=
  (∀ t : ℕ,
      (B.firstGapLeft j).length +
          (B.firstArcCut (B.firstTargetSide s) -
            B.firstArcCut (B.firstGapStartSide j)) = t + 1 →
      ∀ ht : t < (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[t]'ht).IsCompOf (P.label s)) ∧
  (∀ hn :
      (B.firstGapLeft j).length +
          (B.firstArcCut (B.firstTargetSide s) -
            B.firstArcCut (B.firstGapStartSide j)) + 1 <
        (B.firstGapCycle j).length,
      ¬ ((B.firstGapCycle j)[
          (B.firstGapLeft j).length +
            (B.firstArcCut (B.firstTargetSide s) -
              B.firstArcCut (B.firstGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s))

/-- The wrapped endpoint exclusions required for the corresponding second-gap
auxiliary cycle. -/
def SecondGapArcBoundaryExclusion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) : Prop :=
  (∀ t : ℕ,
      (B.secondGapLeft j).length +
          (B.secondArcCut (B.secondTargetSide s) -
            B.secondArcCut (B.secondGapStartSide j)) = t + 1 →
      ∀ ht : t < (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[t]'ht).IsCompOf (P.label s)) ∧
  (∀ hn :
      (B.secondGapLeft j).length +
          (B.secondArcCut (B.secondTargetSide s) -
            B.secondArcCut (B.secondGapStartSide j)) + 1 <
        (B.secondGapCycle j).length,
      ¬ ((B.secondGapCycle j)[
          (B.secondGapLeft j).length +
            (B.secondArcCut (B.secondTargetSide s) -
              B.secondArcCut (B.secondGapStartSide j)) + 1]'hn).IsCompOf
        (P.label s))

/-- In the degenerate empty-cycle model both boundary exclusions are vacuous. -/
theorem firstGapArcBoundaryExclusion_emptyModel
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount) (s : ℕ)
    (hcycle : B.firstGapCycle j = []) :
    FirstGapArcBoundaryExclusion B j s := by
  simp [FirstGapArcBoundaryExclusion, hcycle]

/-- The wrapped empty-cycle model for the endpoint exclusion proposition. -/
theorem secondGapArcBoundaryExclusion_emptyModel
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) (s : ℕ)
    (hcycle : B.secondGapCycle j = []) :
    SecondGapArcBoundaryExclusion B j s := by
  simp [SecondGapArcBoundaryExclusion, hcycle]

/-
/-- DGO's boundary lemma applied under the first endpoint-exclusion input. -/
theorem firstGapArcSource_fullComponent_of_boundaryExclusion
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (h : FirstGapArcBoundaryExclusion B j s) :
    IsComp (B.firstGapLocalLabel j
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1)) := by
  have hsData := Finset.mem_filter.mp hs
  let i := B.firstArcCut (B.firstTargetSide s) -
    B.firstArcCut (B.firstGapStartSide j)
  have hraw := firstGapArcSource_cycleComponent_of_boundary B j s hs h.1 h.2
  have harc : IsPolygonCut
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) :=
    isPolygonCut_arcWord B.firstArc_isCutPath.cut
      (B.firstGap_side_order j) (B.firstGapFinishSide_le j)
  have hcut0 := auxiliaryCycleCut_arc (B.firstGapLeft j)
    (B.firstGapRight j) harc
    (r := B.firstTargetSide s - B.firstGapStartSide j) (by
      have hs' := hsData.2
      omega)
  have harg0 : B.firstGapStartSide j +
      (B.firstTargetSide s - B.firstGapStartSide j) =
      B.firstTargetSide s := by omega
  rw [harg0] at hcut0
  have hr1 : B.firstTargetSide s - B.firstGapStartSide j + 1 ≤
      B.firstGapFinishSide j - B.firstGapStartSide j := by
    omega
  have haux := auxiliaryCycleCut_arc (B.firstGapLeft j)
    (B.firstGapRight j) harc
    (r := B.firstTargetSide s - B.firstGapStartSide j + 1) hr1
  have haux' : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
      ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length +
        (B.firstArcCut (B.firstGapStartSide j +
          (B.firstTargetSide s - B.firstGapStartSide j + 1)) -
          B.firstArcCut (B.firstGapStartSide j)) := by
    simpa only [Nat.add_assoc] using haux
  have hcut1 : B.firstGapCut j
      ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length + i + 1 := by
    have hcutTarget := (B.firstArcCut_target hsData.1).2
    dsimp [firstGapCut, i]
    rw [haux']
    have harg : B.firstGapStartSide j +
        (B.firstTargetSide s - B.firstGapStartSide j + 1) =
        B.firstTargetSide s + 1 := by omega
    rw [harg, hcutTarget]
    have hcutTarget0 := (B.firstArcCut_target hsData.1).1
    rw [← hcutTarget0]
    dsimp [i]
    omega
  dsimp [firstGapCycle, firstGapCut]
  rw [hcut0]
  have hcut1' : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
      ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length + i + 1 := by
    calc
      _ = (B.firstGapLeft j).length +
          (B.firstArcCut (B.firstGapStartSide j +
            (B.firstTargetSide s - B.firstGapStartSide j + 1)) -
            B.firstArcCut (B.firstGapStartSide j)) := by
        exact haux'
      _ = (B.firstGapLeft j).length + i + 1 := by
        have harg1 : B.firstGapStartSide j +
            (B.firstTargetSide s - B.firstGapStartSide j + 1) =
            B.firstTargetSide s + 1 := by omega
        have hcutTarget := (B.firstArcCut_target hsData.1).2
        have hcutTarget0 := (B.firstArcCut_target hsData.1).1
        have hmono := B.firstArc_isCutPath.cut.mono_le hsData.2.1
        rw [harg1, hcutTarget]
        rw [← hcutTarget0]
        dsimp [i]
        omega
  rw [hcut1'] at ⊢
  simpa only [i, B.firstGapLocalLabel_arc j s hs, Nat.add_assoc] using hraw

/-- Wrapped counterpart of `firstGapArcSource_fullComponent_of_boundaryExclusion`. -/
theorem secondGapArcSource_fullComponent_of_boundaryExclusion
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (h : SecondGapArcBoundaryExclusion B j s) :
    IsComp (B.secondGapLocalLabel j
        ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1)) := by
  have hsData := Finset.mem_filter.mp hs
  let i := B.secondArcCut (B.secondTargetSide s) -
    B.secondArcCut (B.secondGapStartSide j)
  have hraw := secondGapArcSource_cycleComponent_of_boundary B j s hs h.1 h.2
  have harc : IsPolygonCut
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) :=
    isPolygonCut_arcWord B.secondArc_isCutPath.cut
      (B.secondGap_side_order j) (B.secondGapFinishSide_le j)
  have hcut0 := auxiliaryCycleCut_arc (B.secondGapLeft j)
    (B.secondGapRight j) harc
    (r := B.secondTargetSide s - B.secondGapStartSide j) (by
      have hs' := hsData.2
      omega)
  have harg0 : B.secondGapStartSide j +
      (B.secondTargetSide s - B.secondGapStartSide j) =
      B.secondTargetSide s := by omega
  rw [harg0] at hcut0
  have hr1 : B.secondTargetSide s - B.secondGapStartSide j + 1 ≤
      B.secondGapFinishSide j - B.secondGapStartSide j := by
    omega
  have haux := auxiliaryCycleCut_arc (B.secondGapLeft j)
    (B.secondGapRight j) harc
    (r := B.secondTargetSide s - B.secondGapStartSide j + 1) hr1
  have haux' : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j)
      ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondGapStartSide j +
          (B.secondTargetSide s - B.secondGapStartSide j + 1)) -
          B.secondArcCut (B.secondGapStartSide j)) := by
    simpa only [Nat.add_assoc] using haux
  have hcut1 : B.secondGapCut j
      ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length + i + 1 := by
    have hcutTarget := (B.secondArcCut_target hsData.1).2
    dsimp [secondGapCut, i]
    rw [haux']
    have harg : B.secondGapStartSide j +
        (B.secondTargetSide s - B.secondGapStartSide j + 1) =
        B.secondTargetSide s + 1 := by omega
    rw [harg, hcutTarget]
    have hcutTarget0 := (B.secondArcCut_target hsData.1).1
    rw [← hcutTarget0]
    dsimp [i]
    omega
  dsimp [secondGapCycle, secondGapCut]
  rw [hcut0]
  have hcut1' : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j)
      ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length + i + 1 := by
    calc
      _ = (B.secondGapLeft j).length +
          (B.secondArcCut (B.secondGapStartSide j +
            (B.secondTargetSide s - B.secondGapStartSide j + 1)) -
            B.secondArcCut (B.secondGapStartSide j)) := by
        exact haux'
      _ = (B.secondGapLeft j).length + i + 1 := by
        have harg1 : B.secondGapStartSide j +
            (B.secondTargetSide s - B.secondGapStartSide j + 1) =
            B.secondTargetSide s + 1 := by omega
        have hcutTarget := (B.secondArcCut_target hsData.1).2
        have hcutTarget0 := (B.secondArcCut_target hsData.1).1
        have hmono := B.secondArc_isCutPath.cut.mono_le hsData.2.1
        rw [harg1, hcutTarget]
        rw [← hcutTarget0]
        dsimp [i]
        omega
  rw [hcut1'] at ⊢
  simpa only [i, B.secondGapLocalLabel_arc j s hs, Nat.add_assoc] using hraw

-/

/-! ## Conditional cut-alignment bridges -/

/-- The two cut equalities needed to transport a component from the raw
auxiliary-cycle coordinates to the balanced-gap coordinates.  This is a
strictly smaller input than a full component-family assertion. -/
def FirstGapArcCutAlignment
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) : Prop :=
  B.firstGapCut j ((B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j)) =
      (B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) ∧
  B.firstGapCut j ((B.firstGapLeft j).length +
      (B.firstTargetSide s - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) + 1

/-- The wrapped version of `FirstGapArcCutAlignment`. -/
def SecondGapArcCutAlignment
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) : Prop :=
  B.secondGapCut j ((B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j)) =
      (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) ∧
  B.secondGapCut j ((B.secondGapLeft j).length +
      (B.secondTargetSide s - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) + 1

/-- The first-gap cut dictionary gives the alignment for every inherited arc
source. -/
theorem firstGapArcCutAlignment_of_source
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j) :
    FirstGapArcCutAlignment B j s := by
  have hsData := Finset.mem_filter.mp hs
  have harc : IsPolygonCut
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (arcWord B.firstArc B.firstArcCut (B.firstGapStartSide j)
        (B.firstGapFinishSide j))
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) :=
    isPolygonCut_arcWord B.firstArc_isCutPath.cut
      (B.firstGap_side_order j) (B.firstGapFinishSide_le j)
  have hcut0 := auxiliaryCycleCut_arc (B.firstGapLeft j)
    (B.firstGapRight j) harc
    (r := B.firstTargetSide s - B.firstGapStartSide j) (by omega)
  have harg0 : B.firstGapStartSide j +
      (B.firstTargetSide s - B.firstGapStartSide j) =
      B.firstTargetSide s := by omega
  rw [harg0] at hcut0
  have hr1 : B.firstTargetSide s - B.firstGapStartSide j + 1 ≤
      B.firstGapFinishSide j - B.firstGapStartSide j := by omega
  have haux1 := auxiliaryCycleCut_arc (B.firstGapLeft j)
    (B.firstGapRight j) harc
    (r := B.firstTargetSide s - B.firstGapStartSide j + 1) hr1
  have hcut1 : auxiliaryCycleCut (B.firstGapLeft j)
      (B.firstGapFinishSide j - B.firstGapStartSide j)
      (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
        B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
      ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1) =
      (B.firstGapLeft j).length +
        (B.firstArcCut (B.firstTargetSide s) -
          B.firstArcCut (B.firstGapStartSide j)) + 1 := by
    calc
      _ = auxiliaryCycleCut (B.firstGapLeft j)
          (B.firstGapFinishSide j - B.firstGapStartSide j)
          (fun r => B.firstArcCut (B.firstGapStartSide j + r) -
            B.firstArcCut (B.firstGapStartSide j)) (B.firstGapRight j)
          ((B.firstGapLeft j).length +
            (B.firstTargetSide s - B.firstGapStartSide j + 1)) := by
        simp only [Nat.add_assoc]
      _ = (B.firstGapLeft j).length +
          (B.firstArcCut (B.firstGapStartSide j +
            (B.firstTargetSide s - B.firstGapStartSide j + 1)) -
            B.firstArcCut (B.firstGapStartSide j)) := haux1
      _ = (B.firstGapLeft j).length +
          (B.firstArcCut (B.firstTargetSide s) -
            B.firstArcCut (B.firstGapStartSide j)) + 1 := by
        have harg1 : B.firstGapStartSide j +
            (B.firstTargetSide s - B.firstGapStartSide j + 1) =
            B.firstTargetSide s + 1 := by omega
        have hcutTarget := (B.firstArcCut_target hsData.1).2
        have hcutTarget0 := (B.firstArcCut_target hsData.1).1
        have hmono := B.firstArc_isCutPath.cut.mono_le hsData.2.1
        rw [harg1, hcutTarget, ← hcutTarget0]
        omega
  refine ⟨?_, ?_⟩
  · simpa only [firstGapCut] using hcut0
  · simpa only [firstGapCut] using hcut1

/-- The wrapped-gap cut dictionary gives the alignment for every inherited arc
source. -/
theorem secondGapArcCutAlignment_of_source
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j) :
    SecondGapArcCutAlignment B j s := by
  have hsData := Finset.mem_filter.mp hs
  have harc : IsPolygonCut
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) :=
    isPolygonCut_arcWord B.secondArc_isCutPath.cut
      (B.secondGap_side_order j) (B.secondGapFinishSide_le j)
  have hcut0 := auxiliaryCycleCut_arc (B.secondGapLeft j)
    (B.secondGapRight j) harc
    (r := B.secondTargetSide s - B.secondGapStartSide j) (by omega)
  have harg0 : B.secondGapStartSide j +
      (B.secondTargetSide s - B.secondGapStartSide j) =
      B.secondTargetSide s := by omega
  rw [harg0] at hcut0
  have hr1 : B.secondTargetSide s - B.secondGapStartSide j + 1 ≤
      B.secondGapFinishSide j - B.secondGapStartSide j := by omega
  have haux1 := auxiliaryCycleCut_arc (B.secondGapLeft j)
    (B.secondGapRight j) harc
    (r := B.secondTargetSide s - B.secondGapStartSide j + 1) hr1
  have hcut1 : auxiliaryCycleCut (B.secondGapLeft j)
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
        B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j)
      ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1) =
      (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondTargetSide s) -
          B.secondArcCut (B.secondGapStartSide j)) + 1 := by
    calc
      _ = auxiliaryCycleCut (B.secondGapLeft j)
          (B.secondGapFinishSide j - B.secondGapStartSide j)
          (fun r => B.secondArcCut (B.secondGapStartSide j + r) -
            B.secondArcCut (B.secondGapStartSide j)) (B.secondGapRight j)
          ((B.secondGapLeft j).length +
            (B.secondTargetSide s - B.secondGapStartSide j + 1)) := by
        simp only [Nat.add_assoc]
      _ = (B.secondGapLeft j).length +
          (B.secondArcCut (B.secondGapStartSide j +
            (B.secondTargetSide s - B.secondGapStartSide j + 1)) -
            B.secondArcCut (B.secondGapStartSide j)) := haux1
      _ = (B.secondGapLeft j).length +
          (B.secondArcCut (B.secondTargetSide s) -
            B.secondArcCut (B.secondGapStartSide j)) + 1 := by
        have harg1 : B.secondGapStartSide j +
            (B.secondTargetSide s - B.secondGapStartSide j + 1) =
            B.secondTargetSide s + 1 := by omega
        have hcutTarget := (B.secondArcCut_target hsData.1).2
        have hcutTarget0 := (B.secondArcCut_target hsData.1).1
        have hmono := B.secondArc_isCutPath.cut.mono_le hsData.2.1
        rw [harg1, hcutTarget, ← hcutTarget0]
        omega
  refine ⟨?_, ?_⟩
  · simpa only [secondGapCut] using hcut0
  · simpa only [secondGapCut] using hcut1

/-- Transport an inherited first-gap component under the endpoint and cut
alignment inputs.  This is the component-family seam in DGO Proposition 4.14. -/
theorem firstGapArcSource_fullComponent_of_boundaryAndCutAlignment
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.first.pieceCount)
    (s : ℕ) (hs : s ∈ B.firstGapArcSources j)
    (hboundary : FirstGapArcBoundaryExclusion B j s)
    (halign : FirstGapArcCutAlignment B j s) :
    IsComp (B.firstGapLocalLabel j
        ((B.firstGapLeft j).length +
          (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCycle j)
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j)))
      (B.firstGapCut j ((B.firstGapLeft j).length +
        (B.firstTargetSide s - B.firstGapStartSide j) + 1)) := by
  have hraw := firstGapArcSource_cycleComponent_of_boundary B j s hs
    hboundary.1 hboundary.2
  simpa only [firstGapCycle, firstGapCut, halign.1, halign.2,
    B.firstGapLocalLabel_arc j s hs] using hraw

/-- Wrapped counterpart of
`firstGapArcSource_fullComponent_of_boundaryAndCutAlignment`. -/
theorem secondGapArcSource_fullComponent_of_boundaryAndCutAlignment
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount)
    (s : ℕ) (hs : s ∈ B.secondGapArcSources j)
    (hboundary : SecondGapArcBoundaryExclusion B j s)
    (halign : SecondGapArcCutAlignment B j s) :
    IsComp (B.secondGapLocalLabel j
        ((B.secondGapLeft j).length +
          (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCycle j)
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j)))
      (B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide s - B.secondGapStartSide j) + 1)) := by
  have hraw := secondGapArcSource_cycleComponent_of_boundary B j s hs
    hboundary.1 hboundary.2
  simpa only [secondGapCycle, secondGapCut, halign.1, halign.2,
    B.secondGapLocalLabel_arc j s hs] using hraw

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
