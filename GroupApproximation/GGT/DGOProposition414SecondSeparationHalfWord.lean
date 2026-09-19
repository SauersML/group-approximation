import GroupApproximation.GGT.DGOProposition414SecondSeparationTransport

/-!
# Isolation of a retained wrapped source, against an arbitrary half-word letter

A source retained in a wrapped gap survives the half cut, so it is a maximal
one-letter component of `secondWord` and is isolated there.  That single fact
already forbids every connection from it to a component of `secondWord` other
than itself, and the connection may be tested at either endpoint of the
offending letter.  This is the form the wrapped separation clause needs, since
the child cycle reads its chord block backwards and then the vertex a step
leaves is one past the letter index.

The rest of the file records where a retained arc source sits in the child
cycle: its cut index, and the parent arc coordinate that index maps to.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- The wrapped half word is its inherited arc followed by the chord, so its
length splits accordingly. -/
theorem secondSeparation_secondWord_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondWord.length = B.secondArc.length + B.chord.length := by
  rw [B.secondWord_eq_append, List.length_append]

/-- **The isolation of a retained wrapped source, tested at either endpoint of
a letter.**  If a source survives the half cut, no `lam`-letter of the half
word other than its own is connected to it, where the connection is measured
at the letter's own vertex or at the next one. -/
theorem secondSeparation_not_connected_of_survives
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) {t : ℕ}
    (hsurv : B.componentPlacement.secondSurvives t)
    {m z : ℕ} (hm : m < B.secondWord.length)
    (hletter : (B.secondWord[m]'hm).IsCompOf (P.label t))
    (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hne : m ≠ B.secondTargetPos t)
    (hconn : Connected D.fam (P.label t) B.secondBase B.secondWord
      (B.secondTargetPos t) z) : False := by
  have hcompS : IsComp (P.label t) B.secondWord (B.secondTargetPos t)
      (B.secondTargetPos t + 1) := hsurv.1
  have hisoS : IsIsolated D.fam (P.label t) B.secondBase B.secondWord
      (B.secondTargetPos t) := hsurv.2
  obtain ⟨a, bb, ha, hb, hcomp⟩ :=
    exists_isComp_of_isCompOf (P.label t) B.secondWord m hm hletter
  have hzle : z ≤ B.secondWord.length := by omega
  have hspan : (vertex B.secondBase B.secondWord a)⁻¹ *
      vertex B.secondBase B.secondWord z ∈ D.fam (P.label t) :=
    span_mem_fam D (P.label t) B.secondBase B.secondWord_letters z hzle a
      (by omega) (fun q hq1 hq2 hq => hcomp.2.2.1 q hq1 (by omega) hq)
  have hconnAZ : Connected D.fam (P.label t) B.secondBase B.secondWord a z :=
    hspan
  have hconnPA : Connected D.fam (P.label t) B.secondBase B.secondWord
      (B.secondTargetPos t) a := connected_trans hconn (connected_symm hconnAZ)
  by_cases hane : a = B.secondTargetPos t
  · have hstep : IsComp (P.label t) B.secondWord a (a + 1) := by
      rw [hane]
      exact hcompS
    have hbb : bb = a + 1 := isComp_end_unique hcomp hstep
    exact hne (by omega)
  · exact hisoS.2 a hane ⟨bb, hcomp⟩ hconnPA

/-! ## The cut index of a retained arc source -/

/-- The cut of a wrapped gap child restricted to its inherited arc is the
parent arc cut, shifted past the left connector. -/
theorem secondSeparation_gapCut_arc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) {r : ℕ}
    (hr : r ≤ B.secondGapFinishSide j - B.secondGapStartSide j) :
    B.secondGapCut j ((B.secondGapLeft j).length + r) =
      (B.secondGapLeft j).length +
        (B.secondArcCut (B.secondGapStartSide j + r) -
          B.secondArcCut (B.secondGapStartSide j)) := by
  have harc : IsPolygonCut
      (B.secondGapFinishSide j - B.secondGapStartSide j)
      (arcWord B.secondArc B.secondArcCut (B.secondGapStartSide j)
        (B.secondGapFinishSide j))
      (fun s => B.secondArcCut (B.secondGapStartSide j + s) -
        B.secondArcCut (B.secondGapStartSide j)) :=
    isPolygonCut_arcWord B.secondArc_isCutPath.cut
      (B.secondGap_side_order j) (B.secondGapFinishSide_le j)
  exact auxiliaryCycleCut_arc (B.secondGapLeft j) (B.secondGapRight j) harc hr

/-- The parent arc coordinate of a retained arc source of a wrapped gap. -/
theorem secondSeparation_arcSource_cut
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) {t : ℕ}
    (ht : t ∈ B.secondGapArcSources j) :
    B.secondGapCut j ((B.secondGapLeft j).length +
        (B.secondTargetSide t - B.secondGapStartSide j)) =
      (B.secondGapLeft j).length +
        (B.secondTargetPos t - B.secondArcCut (B.secondGapStartSide j)) := by
  classical
  have hdata := Finset.mem_filter.mp ht
  have hrange := hdata.2
  have hct := B.secondArcCut_target hdata.1
  have hcut := B.secondSeparation_gapCut_arc j
    (r := B.secondTargetSide t - B.secondGapStartSide j) (by omega)
  have harg : B.secondGapStartSide j +
      (B.secondTargetSide t - B.secondGapStartSide j) =
      B.secondTargetSide t := by omega
  rw [harg, hct.1] at hcut
  exact hcut

/-- A retained arc source of a wrapped gap sits strictly inside the child arc
block, at the parent arc coordinate. -/
theorem secondSeparation_arcSource_offset
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (j : Fin B.brokenAssignment.index.second.pieceCount) {t : ℕ}
    (ht : t ∈ B.secondGapArcSources j) :
    B.secondArcCut (B.secondGapStartSide j) ≤ B.secondTargetPos t ∧
      B.secondTargetPos t + 1 ≤ B.secondArcCut (B.secondGapFinishSide j) := by
  classical
  have hdata := Finset.mem_filter.mp ht
  have hrange := hdata.2
  have hct := B.secondArcCut_target hdata.1
  have hmono1 : B.secondArcCut (B.secondGapStartSide j) ≤
      B.secondArcCut (B.secondTargetSide t) :=
    B.secondArc_isCutPath.cut.mono_le hrange.1
  have hmono2 : B.secondArcCut (B.secondTargetSide t + 1) ≤
      B.secondArcCut (B.secondGapFinishSide j) :=
    B.secondArc_isCutPath.cut.mono_le (by omega)
  omega

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
