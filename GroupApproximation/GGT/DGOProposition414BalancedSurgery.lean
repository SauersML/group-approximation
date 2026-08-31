import GroupApproximation.GGT.DGOProposition414BalancedPlacement
import GroupApproximation.GGT.DGOProposition414OrientedSegment

/-!
# Exact interval surgery over a balanced split

This file is the bookkeeping boundary between the two geometric halves and
the exact Proposition 4.14 producer.  The interval geometry is indexed by the
canonical broken-component assignment.  Target embeddings are recorded
separately on the disjoint first and second target sets; their global owner and
target-index maps are derived from the target cover.
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
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : BalancedSplitComponentPlacement D hsymm b hδ P B)
    (A : TwoHalfBrokenAssignment C.firstTarget C.secondTarget
      C.firstSurvives C.secondSurvives C.firstPos C.secondPos
      B.chord.length) where
  intervals : TwoHalfIntervalSurgery D hsymm b A.index
    B.firstBase (vertex P.basepoint P.word B.secondVertex)
    B.chord B.chord_geodesic
  arc_partition :
    (∑ j, (intervals.first j).arcSides) +
      ∑ j, (intervals.second j).arcSides = n
  first_connectors : ∀ j,
    (intervals.first j).left.length + (intervals.first j).right.length ≤ 2
  second_connectors : ∀ j,
    (intervals.second j).left.length + (intervals.second j).right.length ≤ 2
  first_small : ∀ j,
    5 * ((intervals.toPathInput).first j).sideCount ≤ 4 * n
  second_small : ∀ j,
    5 * ((intervals.toPathInput).second j).sideCount ≤ 4 * n

namespace BalancedSplitIntervalSurgery

/-- The balanced split uses the original chord itself, so the corrected
`SideBounds` chord-length field is definitional. -/
theorem sideBounds
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    {C : BalancedSplitComponentPlacement D hsymm b hδ P B}
    {A : TwoHalfBrokenAssignment C.firstTarget C.secondTarget
      C.firstSurvives C.secondSurvives C.firstPos C.secondPos
      B.chord.length}
    (S : BalancedSplitIntervalSurgery D hsymm b hδ P B C A) :
    TwoHalfIntervalSurgery.SideBounds S.intervals n where
  arc_partition := S.arc_partition
  first_connectors := S.first_connectors
  second_connectors := S.second_connectors
  chord_length := rfl
  first_small := S.first_small
  second_small := S.second_small

end BalancedSplitIntervalSurgery

/-- Survivor-or-quadrilateral placement into the actual child targets.

The two halves retain separate owners.  This makes the injectivity statement
local to the corresponding target partition and prevents accidental mixing of
the two interval coordinate systems. -/
structure BalancedSplitTargetEmbedding
    (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (b : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    {n : ℕ} (P : SumBoundInput D (b : ℝ) n) {k R : ℕ}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (C : BalancedSplitComponentPlacement D hsymm b hδ P B)
    (A : TwoHalfBrokenAssignment C.firstTarget C.secondTarget
      C.firstSurvives C.secondSurvives C.firstPos C.secondPos
      B.chord.length)
    (S : BalancedSplitIntervalSurgery D hsymm b hδ P B C A) where
  firstOwner : ℕ → Fin A.index.first.pieceCount
  secondOwner : ℕ → Fin A.index.second.pieceCount
  firstTargetIndex : Fin A.index.first.pieceCount → ℕ → ℕ
  secondTargetIndex : Fin A.index.second.pieceCount → ℕ → ℕ
  first_mem : ∀ s ∈ C.firstTarget,
    firstTargetIndex (firstOwner s) s ∈
      ((S.intervals.toPathInput.family).firstChildren (firstOwner s)).target
  second_mem : ∀ s ∈ C.secondTarget,
    secondTargetIndex (secondOwner s) s ∈
      ((S.intervals.toPathInput.family).secondChildren (secondOwner s)).target
  first_label : ∀ s ∈ C.firstTarget,
    ((S.intervals.toPathInput.family).firstChildren (firstOwner s)).label
      (firstTargetIndex (firstOwner s) s) = P.label s
  second_label : ∀ s ∈ C.secondTarget,
    ((S.intervals.toPathInput.family).secondChildren (secondOwner s)).label
      (secondTargetIndex (secondOwner s) s) = P.label s
  first_span : ∀ s ∈ C.firstTarget,
    P.span s =
      ((S.intervals.toPathInput.family).firstChildren (firstOwner s)).sideSpan
        (firstTargetIndex (firstOwner s) s)
  second_span : ∀ s ∈ C.secondTarget,
    P.span s =
      ((S.intervals.toPathInput.family).secondChildren (secondOwner s)).sideSpan
        (secondTargetIndex (secondOwner s) s)
  first_injective : ∀ j, Set.InjOn (firstTargetIndex j)
    (↑(C.firstTarget.filter fun s => firstOwner s = j) : Set ℕ)
  second_injective : ∀ j, Set.InjOn (secondTargetIndex j)
    (↑(C.secondTarget.filter fun s => secondOwner s = j) : Set ℕ)

namespace BalancedSplitTargetEmbedding

noncomputable def owner
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    {C : BalancedSplitComponentPlacement D hsymm b hδ P B}
    {A : TwoHalfBrokenAssignment C.firstTarget C.secondTarget
      C.firstSurvives C.secondSurvives C.firstPos C.secondPos
      B.chord.length}
    {S : BalancedSplitIntervalSurgery D hsymm b hδ P B C A}
    (E : BalancedSplitTargetEmbedding D hsymm b hδ P B C A S) (s : ℕ) :
    Sum (Fin A.index.first.pieceCount) (Fin A.index.second.pieceCount) := by
  classical
  exact if s ∈ C.firstTarget then Sum.inl (E.firstOwner s)
    else Sum.inr (E.secondOwner s)

def targetIndex
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    {C : BalancedSplitComponentPlacement D hsymm b hδ P B}
    {A : TwoHalfBrokenAssignment C.firstTarget C.secondTarget
      C.firstSurvives C.secondSurvives C.firstPos C.secondPos
      B.chord.length}
    {S : BalancedSplitIntervalSurgery D hsymm b hδ P B C A}
    (E : BalancedSplitTargetEmbedding D hsymm b hδ P B C A S) :
    Sum (Fin A.index.first.pieceCount) (Fin A.index.second.pieceCount) →
      ℕ → ℕ
  | Sum.inl j => E.firstTargetIndex j
  | Sum.inr j => E.secondTargetIndex j

private theorem second_mem_of_target_not_first
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    {C : BalancedSplitComponentPlacement D hsymm b hδ P B}
    {s : ℕ} (hs : s ∈ P.target) (hfirst : s ∉ C.firstTarget) :
    s ∈ C.secondTarget := by
  rw [C.target_cover] at hs
  simpa [hfirst] using hs

/-- The two local embeddings assemble into the precise global embedding
hypotheses consumed by `auxiliaryCycleFamilyCertificate_of_intervalSurgery`. -/
noncomputable def certificate
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    {C : BalancedSplitComponentPlacement D hsymm b hδ P B}
    {A : TwoHalfBrokenAssignment C.firstTarget C.secondTarget
      C.firstSurvives C.secondSurvives C.firstPos C.secondPos
      B.chord.length}
    {S : BalancedSplitIntervalSurgery D hsymm b hδ P B C A}
    (E : BalancedSplitTargetEmbedding D hsymm b hδ P B C A S) :
    AuxiliaryCycleFamilyCertificate D hsymm b hδ n P.basepoint P.word P.cut
      P.target P.label := by
  classical
  apply TwoHalfIntervalSurgery.auxiliaryCycleFamilyCertificate_of_intervalSurgery
    D hsymm b hδ A.index B.firstBase
    (vertex P.basepoint P.word B.secondVertex) B.chord B.chord_geodesic
    S.intervals n P.basepoint P.word P.cut P.target P.label
    E.owner E.targetIndex
  · intro s hs
    by_cases hfirst : s ∈ C.firstTarget
    · simpa [owner, targetIndex, hfirst] using E.first_mem s hfirst
    · have hsecond := second_mem_of_target_not_first hs hfirst
      simpa [owner, targetIndex, hfirst] using E.second_mem s hsecond
  · intro s hs
    by_cases hfirst : s ∈ C.firstTarget
    · simpa [owner, targetIndex, hfirst] using E.first_label s hfirst
    · have hsecond := second_mem_of_target_not_first hs hfirst
      simpa [owner, targetIndex, hfirst] using E.second_label s hsecond
  · intro s hs
    by_cases hfirst : s ∈ C.firstTarget
    · simpa [SumBoundInput.span, owner, targetIndex, hfirst] using
        E.first_span s hfirst
    · have hsecond := second_mem_of_target_not_first hs hfirst
      simpa [SumBoundInput.span, owner, targetIndex, hfirst] using
        E.second_span s hsecond
  · intro q
    cases q with
    | inl j =>
        intro s hs t ht heq
        have hsTarget := (Finset.mem_filter.mp hs).1
        have htTarget := (Finset.mem_filter.mp ht).1
        have hsOwner := (Finset.mem_filter.mp hs).2
        have htOwner := (Finset.mem_filter.mp ht).2
        have hsFirst : s ∈ C.firstTarget := by
          by_contra h
          simp [owner, h] at hsOwner
        have htFirst : t ∈ C.firstTarget := by
          by_contra h
          simp [owner, h] at htOwner
        apply E.first_injective j
        · exact Finset.mem_filter.mpr ⟨hsFirst, by simpa [owner, hsFirst] using hsOwner⟩
        · exact Finset.mem_filter.mpr ⟨htFirst, by simpa [owner, htFirst] using htOwner⟩
        · simpa [targetIndex] using heq
    | inr j =>
        intro s hs t ht heq
        have hsTarget := (Finset.mem_filter.mp hs).1
        have htTarget := (Finset.mem_filter.mp ht).1
        have hsOwner := (Finset.mem_filter.mp hs).2
        have htOwner := (Finset.mem_filter.mp ht).2
        have hsFirst : s ∉ C.firstTarget := by
          intro h
          simp [owner, h] at hsOwner
        have htFirst : t ∉ C.firstTarget := by
          intro h
          simp [owner, h] at htOwner
        have hsSecond := second_mem_of_target_not_first hsTarget hsFirst
        have htSecond := second_mem_of_target_not_first htTarget htFirst
        apply E.second_injective j
        · exact Finset.mem_filter.mpr
            ⟨hsSecond, by simpa [owner, hsFirst] using hsOwner⟩
        · exact Finset.mem_filter.mpr
            ⟨htSecond, by simpa [owner, htFirst] using htOwner⟩
        · simpa [targetIndex] using heq
  · exact S.sideBounds

/-- On an extremal polygon, the exact balanced-surgery certificate exports the
numerical subdivision tuple used by the corrected Proposition 4.14 assembly. -/
theorem exists_quadraticCostSubdivisionData
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    {B : BalancedSplitData D hsymm b hδ P k R}
    {C : BalancedSplitComponentPlacement D hsymm b hδ P B}
    {A : TwoHalfBrokenAssignment C.firstTarget C.secondTarget
      C.firstSurvives C.secondSurvives C.firstPos C.secondPos
      B.chord.length}
    {S : BalancedSplitIntervalSurgery D hsymm b hδ P B C A}
    (E : BalancedSplitTargetEmbedding D hsymm b hδ P B C A S)
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
    hextremal E.certificate

end BalancedSplitTargetEmbedding

end DGOProposition414
end GGT
end GroupApproximation
