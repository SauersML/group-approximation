import GroupApproximation.GGT.DGOProposition414GapLocalTarget

/-!
# Quasigeodesicity of the inherited balanced arcs

Inserting the two balanced chord endpoints can split an original distinguished
side.  A fragment not represented by the transported target set is trivial,
while every other non-target child side is a subpath of an original
off-target side.  This file proves that reduction for the ordinary first arc.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Away from the first inserted corner, the refined first-arc cut is the
original cut with its side index shifted by the insertion. -/
theorem refinedCut_firstArc_of_pos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs0 : 0 < s) (hs : s ≤ B.secondSide - B.firstSide) :
    B.refinedCut (B.firstSide + 1 + s) = P.cut (B.firstSide + s) := by
  have horder := B.side_order
  unfold refinedCut splitPairCut insertPointCut
  rw [if_pos (show B.firstSide + 1 + s ≤ B.secondSide + 1 by omega),
    if_neg (show ¬B.firstSide + 1 + s ≤ B.firstSide by omega),
    if_neg (show B.firstSide + 1 + s ≠ B.firstSide + 1 by omega)]
  congr 1
  omega

/-- The first child cut starts at the inserted vertex. -/
@[simp] theorem firstArcCut_zero
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstArcCut 0 = 0 := by
  simp [firstArcCut]

/-- Positive first-arc side coordinates start at the corresponding original
polygon corner. -/
theorem firstArcCut_of_pos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs0 : 0 < s) (hs : s ≤ B.secondSide - B.firstSide) :
    B.firstArcCut s = P.cut (B.firstSide + s) - B.firstVertex := by
  have hbase : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  simp only [firstArcCut]
  rw [B.refinedCut_firstArc_of_pos hs0 hs, hbase]

/-- Before the second inserted corner, the finish of a first-arc side is the
next original polygon corner. -/
theorem firstArcCut_succ_of_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s < B.secondSide - B.firstSide) :
    B.firstArcCut (s + 1) =
      P.cut (B.firstSide + s + 1) - B.firstVertex := by
  rw [B.firstArcCut_of_pos (by omega) (by omega)]
  congr 2
  omega

/-- The last first-arc side finishes at the second inserted chord endpoint. -/
theorem firstArcCut_last_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstArcCut (B.secondSide - B.firstSide + 1) =
      B.secondVertex - B.firstVertex := by
  have hbase : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hend : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  simp only [firstArcCut]
  rw [show B.firstSide + 1 + (B.secondSide - B.firstSide + 1) =
      B.secondSide + 2 by omega,
    hend, hbase]

/-- A first-arc side omitted from the transported target image either came
from an original off-target side or is a trivial fragment at an inserted
endpoint. -/
theorem firstArc_offTarget_source_or_trivial
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s < B.secondSide - B.firstSide + 1)
    (hsTarget : s ∉ B.firstArcTargetSides) :
    B.firstSide + s ∉ P.target ∨
      B.firstArcCut (s + 1) = B.firstArcCut s := by
  classical
  by_cases hparent : B.firstSide + s ∈ P.target
  · right
    by_cases hinside : B.targetInFirstArc (B.firstSide + s)
    · have hfirst : B.firstSide + s ∈ B.firstTarget := by
        simp [firstTarget, hparent, hinside]
      have himage : B.firstTargetSide (B.firstSide + s) ∈
          B.firstArcTargetSides := by
        exact Finset.mem_image.mpr ⟨B.firstSide + s, hfirst, rfl⟩
      have hside : B.firstTargetSide (B.firstSide + s) = s := by
        simp [firstTargetSide]
      exact (hsTarget (hside ▸ himage)).elim
    · have hedge := P.target_edge (B.firstSide + s) hparent
      unfold targetInFirstArc at hinside
      by_cases hs0 : s = 0
      · subst s
        have hfinishLe : P.cut (B.firstSide + 1) ≤ B.secondVertex := by
          exact (P.polygonCut.mono_le (show B.firstSide + 1 ≤
            B.secondSide by omega)).trans B.secondVertex_mem.1
        have hnotStart : ¬B.firstVertex ≤ P.cut B.firstSide := by
          exact fun hstart => hinside ⟨hstart, hfinishLe⟩
        have hvertex : B.firstVertex = P.cut (B.firstSide + 1) := by
          omega
        rw [B.firstArcCut_zero, B.firstArcCut_succ_of_lt (by omega),
          show B.firstSide + 0 + 1 = B.firstSide + 1 by omega,
          hvertex, Nat.sub_self]
      · by_cases hlast : s = B.secondSide - B.firstSide
        · have hsource : B.firstSide + s = B.secondSide := by omega
          have hstartLe : B.firstVertex ≤ P.cut (B.firstSide + s) := by
            exact B.firstVertex_mem.2.trans
              (P.polygonCut.mono_le (show B.firstSide + 1 ≤
                B.firstSide + s by omega))
          have hnotFinish : ¬P.cut (B.firstSide + s + 1) ≤
              B.secondVertex := by
            exact fun hfinish => hinside ⟨hstartLe, hfinish⟩
          have hvertex : B.secondVertex = P.cut (B.firstSide + s) := by
            have hleft := B.secondVertex_mem.1
            rw [← hsource] at hleft
            omega
          rw [B.firstArcCut_last_succ,
            B.firstArcCut_of_pos hs0 (by omega), hvertex]
        · have hstartLe : B.firstVertex ≤ P.cut (B.firstSide + s) := by
            exact B.firstVertex_mem.2.trans
              (P.polygonCut.mono_le (show B.firstSide + 1 ≤
                B.firstSide + s by omega))
          have hfinishLe : P.cut (B.firstSide + s + 1) ≤
              B.secondVertex := by
            exact (P.polygonCut.mono_le (show B.firstSide + s + 1 ≤
              B.secondSide by omega)).trans B.secondVertex_mem.1
          exact (hinside ⟨hstartLe, hfinishLe⟩).elim
  · exact Or.inl hparent

/-- The ordinary inherited first arc satisfies the exact off-target
quasigeodesic premise required by every first-gap restriction. -/
theorem firstArc_quasi
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    ∀ s : ℕ, s < B.secondSide - B.firstSide + 1 →
      s ∉ B.firstArcTargetSides → ∀ p q : ℕ,
      B.firstArcCut s ≤ p → p ≤ q → q ≤ B.firstArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex B.firstBase B.firstArc p)
          (vertex B.firstBase B.firstArc q) : ℕ) : ℝ) := by
  intro s hs hsTarget p q hp hpq hq
  rcases B.firstArc_offTarget_source_or_trivial hs hsTarget with
      hparent | htrivial
  · have hsourceLt : B.firstSide + s < n := by omega
    have hleft : P.cut (B.firstSide + s) ≤ B.firstVertex + p := by
      by_cases hs0 : s = 0
      · subst s
        simpa using B.firstVertex_mem.1.trans (Nat.add_le_add_left hp _)
      · have hcut := B.firstArcCut_of_pos hs0 (by omega)
        rw [hcut] at hp
        have hvertex := B.firstVertex_mem.2.trans
          (P.polygonCut.mono_le (show B.firstSide + 1 ≤
            B.firstSide + s by omega))
        omega
    have hright : B.firstVertex + q ≤ P.cut (B.firstSide + s + 1) := by
      by_cases hlast : s = B.secondSide - B.firstSide
      · rw [hlast, B.firstArcCut_last_succ] at hq
        have hvertex := B.secondVertex_mem.2
        omega
      · have hcut := B.firstArcCut_succ_of_lt (by omega)
        rw [hcut] at hq
        have hvertex := B.firstVertex_mem.2.trans
          (P.polygonCut.mono_le (show B.firstSide + 1 ≤
            B.firstSide + s + 1 by omega))
        omega
    have hparentQuasi := P.quasi (B.firstSide + s) hsourceLt hparent
      (B.firstVertex + p) (B.firstVertex + q) hleft
      (Nat.add_le_add_left hpq _) hright
    have hbase : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hqArc : q ≤ B.refinedCut (B.secondSide + 2) -
        B.refinedCut (B.firstSide + 1) := by
      have hsideLe : s + 1 ≤ B.secondSide - B.firstSide + 1 := by omega
      have hcutLe := B.firstArc_isCutPath.cut.mono_le hsideLe
      have hqEnd := hq.trans hcutLe
      simpa only [firstArcCut,
        show B.firstSide + 1 + (B.secondSide - B.firstSide + 1) =
          B.secondSide + 2 by omega] using hqEnd
    have hpArc : p ≤ B.refinedCut (B.secondSide + 2) -
        B.refinedCut (B.firstSide + 1) := hpq.trans hqArc
    have hvp := vertex_arcWord P.word P.basepoint B.refinedCut hpArc
    have hvq := vertex_arcWord P.word P.basepoint B.refinedCut hqArc
    have hdiff : B.firstVertex + q - (B.firstVertex + p) = q - p := by
      omega
    simpa only [firstBase, firstArc, hbase, hvp, hvq, hdiff] using
      hparentQuasi
  · have hpqEq : p = q := by omega
    subst q
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    simpa only [Nat.sub_self, Nat.cast_zero, wordDist_self, zero_sub] using
      (neg_nonpos.mpr hb0)

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
