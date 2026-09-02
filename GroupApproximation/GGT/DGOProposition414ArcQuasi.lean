import GroupApproximation.GGT.DGOProposition414GapLocalTarget
import GroupApproximation.GGT.DGOAssemblyVertices
import GroupApproximation.GGT.DGOIsolatedComponentRotate

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
open GroupApproximation.GGT.OsinComponents
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

/-- The last first-arc side finishes at the second inserted chord endpoint. -/
theorem firstArcCut_last_succ
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstArcCut (B.secondSide - B.firstSide + 1) =
      B.secondVertex - B.firstVertex := by
  have horder := B.side_order
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
  have horder := B.side_order
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
        simp only [Nat.add_zero] at hedge hinside
        have hfinishLe : P.cut (B.firstSide + 1) ≤ B.secondVertex := by
          exact (P.polygonCut.mono_le (show B.firstSide + 1 ≤
            B.secondSide by omega)).trans B.secondVertex_mem.1
        have hnotStart : ¬B.firstVertex ≤ P.cut B.firstSide := by
          exact fun hstart => hinside ⟨hstart, hfinishLe⟩
        have hvertex : B.firstVertex = P.cut (B.firstSide + 1) := by
          have hleft := B.firstVertex_mem.1
          have hright := B.firstVertex_mem.2
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
          subst s
          rw [B.firstArcCut_last_succ,
            B.firstArcCut_of_pos (by omega) (le_refl _), hvertex]
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
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  intro s hs hsTarget p q hp hpq hq
  rcases B.firstArc_offTarget_source_or_trivial hs hsTarget with
      hparent | htrivial
  · have hsourceLt : B.firstSide + s < n := by omega
    have hleft : P.cut (B.firstSide + s) ≤ B.firstVertex + p := by
      by_cases hs0 : s = 0
      · subst s
        simpa only [Nat.add_zero] using
          B.firstVertex_mem.1.trans (Nat.le_add_right B.firstVertex p)
      · have hcut := B.firstArcCut_of_pos (by omega) (by omega)
        rw [hcut] at hp
        have hvertex := B.firstVertex_mem.2.trans
          (P.polygonCut.mono_le (show B.firstSide + 1 ≤
            B.firstSide + s by omega))
        omega
    have hright : B.firstVertex + q ≤ P.cut (B.firstSide + s + 1) := by
      have hvertices := B.split_vertices_ordered
      by_cases hlast : s = B.secondSide - B.firstSide
      · rw [hlast, B.firstArcCut_last_succ] at hq
        have hvertex := B.secondVertex_mem.2
        omega
      · have hslt : s < B.secondSide - B.firstSide := by omega
        have hcut := B.firstArcCut_succ_of_lt hslt
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

/-! ## The wrapped complementary arc -/

/-- Original polygon side read at a wrapped second-arc coordinate. -/
def secondArcSource
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : ℕ :=
  if s < n - B.secondSide then B.secondSide + s
  else s - (n - B.secondSide)

/-- Positive cut coordinates in the terminal suffix are original corners
after the second selected side. -/
theorem refinedCut_secondArc_of_pos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs0 : 0 < s) (hs : s ≤ n - B.secondSide) :
    B.refinedCut (B.secondSide + 2 + s) =
      P.cut (B.secondSide + s) := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  unfold refinedCut splitPairCut insertPointCut
  rw [if_neg (show ¬B.secondSide + 2 + s ≤ B.secondSide + 1 by omega),
    if_neg (show B.secondSide + 2 + s ≠ B.secondSide + 2 by omega),
    if_neg (show ¬B.secondSide + 2 + s - 1 ≤ B.firstSide by omega),
    if_neg (show B.secondSide + 2 + s - 1 ≠
      B.firstSide + 1 by omega)]
  congr 1
  omega

/-- Refined corners before the first selected side are unchanged. -/
theorem refinedCut_before_first
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ≤ B.firstSide) :
    B.refinedCut s = P.cut s := by
  have horder := B.side_order
  unfold refinedCut splitPairCut insertPointCut
  rw [if_pos (show s ≤ B.secondSide + 1 by omega), if_pos hs]

/-- The wrapped cut begins at the second inserted endpoint. -/
@[simp] theorem secondArcCut_zero
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondArcCut 0 = 0 := by
  simp [secondArcCut, appendCut]

/-- Positive wrapped coordinates up to the old word seam are shifted suffix
corners of the original polygon. -/
theorem secondArcCut_of_pos_le_tail
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs0 : 0 < s) (hs : s ≤ n - B.secondSide) :
    B.secondArcCut s =
      P.cut (B.secondSide + s) - B.secondVertex := by
  have houter : s ≤
      (n + 2 - (B.secondSide + 2)) + (B.firstSide + 1) := by omega
  have hinner : s ≤ n + 2 - (B.secondSide + 2) := by omega
  have hbase : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  simp only [secondArcCut,
    appendCut_apply_of_le _ _ _ _ houter,
    appendCut_apply_of_le _ _ _ _ hinner]
  rw [B.refinedCut_secondArc_of_pos hs0 (by omega), hbase]

/-- After crossing the old word seam, the wrapped cut is the suffix length
plus the corresponding original prefix corner. -/
theorem secondArcCut_tail_add
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R r : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hr : r ≤ B.firstSide) :
    B.secondArcCut (n - B.secondSide + r) =
      (P.word.length - B.secondVertex) + P.cut r := by
  have hsecond := B.secondSide_lt
  let tail := n + 2 - (B.secondSide + 2)
  have htail : tail = n - B.secondSide := by dsimp [tail]; omega
  have htail0 : 0 < tail := by dsimp [tail]; omega
  have houter : tail + r ≤ tail + (B.firstSide + 1) := by omega
  have hzero : B.refinedCut 0 = 0 := by
    rw [B.refinedCut_before_first (Nat.zero_le _), P.polygonCut.start]
  have hinner := appendCut_apply_add
    (fun s => B.refinedCut (B.secondSide + 2 + s) -
      B.refinedCut (B.secondSide + 2)) B.refinedCut tail r hzero
  have hbase : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hend : B.refinedCut (B.secondSide + 2 + tail) =
      P.word.length := by
    rw [B.refinedCut_secondArc_of_pos htail0 (by dsimp [tail]; omega)]
    have hindex : B.secondSide + tail = n := by dsimp [tail]; omega
    rw [hindex, P.polygonCut.finish]
  rw [← htail]
  simp only [secondArcCut,
    appendCut_apply_of_le _ _ _ _ houter, hinner, hend, hbase,
    B.refinedCut_before_first hr]

/-- The final wrapped side ends at the first inserted chord endpoint. -/
theorem secondArcCut_finish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondArcCut ((n - B.secondSide) + B.firstSide + 1) =
      (P.word.length - B.secondVertex) + B.firstVertex := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  rw [B.secondArc_isCutPath.cut.finish]
  have hfirstLe : B.firstVertex ≤ P.word.length :=
    B.firstVertex_mem.2.trans
      (P.polygonCut.le_length (show B.firstSide + 1 ≤ n by omega))
  simp [secondArc, List.length_append, List.length_drop, List.length_take,
    Nat.min_eq_left hfirstLe]

/-- The wrapped source map is inverse to the transported second-side
coordinate throughout the full complementary side range. -/
theorem secondTargetSide_secondArcSource
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s < (n - B.secondSide) + B.firstSide + 1) :
    B.secondTargetSide (B.secondArcSource s) = s := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  by_cases htail : s < n - B.secondSide
  · simp [secondArcSource, secondTargetSide, htail]
  · have hsource : s - (n - B.secondSide) ≤ B.firstSide := by omega
    have hbefore : ¬B.secondSide ≤ s - (n - B.secondSide) := by omega
    simp [secondArcSource, secondTargetSide, htail, hbefore]
    omega

/-- A wrapped side omitted from the transported target image either came
from an original off-target side or is a trivial fragment at an inserted
endpoint. -/
theorem secondArc_offTarget_source_or_trivial
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s < (n - B.secondSide) + B.firstSide + 1)
    (hsTarget : s ∉ B.secondArcTargetSides) :
    B.secondArcSource s ∉ P.target ∨
      B.secondArcCut (s + 1) = B.secondArcCut s := by
  classical
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  by_cases hparent : B.secondArcSource s ∈ P.target
  · right
    have hunion : B.secondArcSource s ∈ B.firstTarget ∪ B.secondTarget := by
      rw [← B.target_partition.2]
      exact hparent
    rcases Finset.mem_union.mp hunion with hfirst | hsecond
    · have hinside := (Finset.mem_filter.mp hfirst).2
      unfold targetInFirstArc at hinside
      by_cases htail : s < n - B.secondSide
      · have hsource : B.secondArcSource s = B.secondSide + s := by
          simp [secondArcSource, htail]
        have hs0 : s = 0 := by
          by_contra hs0
          have hmono := P.polygonCut.mono_le
            (show B.secondSide + 1 ≤ B.secondArcSource s by
              rw [hsource]
              omega)
          have hedge := P.target_edge (B.secondArcSource s) hparent
          omega
        subst s
        have hvertex : B.secondVertex = P.cut (B.secondSide + 1) := by
          have hright := B.secondVertex_mem.2
          simpa only [secondArcSource, if_pos (show 0 < n - B.secondSide by
            omega), Nat.add_zero] using le_antisymm hright hinside.2
        rw [B.secondArcCut_zero,
          B.secondArcCut_of_pos_le_tail (by omega) (by omega), hvertex,
          Nat.sub_self]
      · have hsource : B.secondArcSource s =
            s - (n - B.secondSide) := by
          simp [secondArcSource, htail]
        have hsourceLe : B.secondArcSource s ≤ B.firstSide := by
          rw [hsource]
          omega
        have hsourceEq : B.secondArcSource s = B.firstSide := by
          by_contra hne
          have hmono := P.polygonCut.mono_le
            (show B.secondArcSource s + 1 ≤ B.firstSide by omega)
          have hedge := P.target_edge (B.secondArcSource s) hparent
          omega
        have hsLast : s = (n - B.secondSide) + B.firstSide := by
          rw [hsource, hsourceEq]
          omega
        have hvertex : B.firstVertex = P.cut B.firstSide := by
          have hleft := B.firstVertex_mem.1
          have hstart : B.firstVertex ≤ P.cut B.firstSide := by
            rw [← hsourceEq]
            exact hinside.1
          exact le_antisymm hstart hleft
        rw [hsLast, B.secondArcCut_finish,
          show (n - B.secondSide) + B.firstSide =
            n - B.secondSide + B.firstSide by rfl,
          B.secondArcCut_tail_add (le_refl _), hvertex]
    · have himage : B.secondTargetSide (B.secondArcSource s) ∈
          B.secondArcTargetSides :=
        Finset.mem_image.mpr ⟨B.secondArcSource s, hsecond, rfl⟩
      exact (hsTarget ((B.secondTargetSide_secondArcSource hs) ▸
        himage)).elim
  · exact Or.inl hparent

/-- The wrapped inherited arc satisfies the exact off-target quasigeodesic
premise required by every complementary-gap restriction. -/
theorem secondArc_quasi
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    ∀ s : ℕ, s < (n - B.secondSide) + B.firstSide + 1 →
      s ∉ B.secondArcTargetSides → ∀ p q : ℕ,
      B.secondArcCut s ≤ p → p ≤ q → q ≤ B.secondArcCut (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex B.secondBase B.secondArc p)
          (vertex B.secondBase B.secondArc q) : ℕ) : ℝ) := by
  have horder := B.side_order
  have hsecond := B.secondSide_lt
  intro s hs hsTarget p q hp hpq hq
  rcases B.secondArc_offTarget_source_or_trivial hs hsTarget with
      hparent | htrivial
  · have hsecondLe : B.secondVertex ≤ P.word.length :=
      B.secondVertex_mem.2.trans
        (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
    have hqArc : q ≤
        (P.word.length - B.secondVertex) + B.firstVertex := by
      have hsideLe : s + 1 ≤
          (n - B.secondSide) + B.firstSide + 1 := by omega
      have hcutLe := B.secondArc_isCutPath.cut.mono_le hsideLe
      have hqEnd := hq.trans hcutLe
      rwa [B.secondArcCut_finish] at hqEnd
    have hpArc : p ≤
        (P.word.length - B.secondVertex) + B.firstVertex := hpq.trans hqArc
    have hleftCorner : B.refinedCut (B.firstSide + 1) =
        B.firstVertex := by
      simp [refinedCut, splitPairCut_left B.side_order]
    have hrightCorner : B.refinedCut (B.secondSide + 2) =
        B.secondVertex := by
      simp [refinedCut, splitPairCut_right]
    have hcornerOrder : B.refinedCut (B.firstSide + 1) ≤
        B.refinedCut (B.secondSide + 2) := by
      rw [hleftCorner, hrightCorner]
      exact B.split_vertices_ordered
    have hvpRot := vertex_secondHalf_rotWord P.word P.basepoint B.refinedCut
      hcornerOrder (by rwa [hrightCorner])
      (by simpa only [hleftCorner, hrightCorner] using hpArc)
      ([] : List (RelLetter G Λ))
    have hvqRot := vertex_secondHalf_rotWord P.word P.basepoint B.refinedCut
      hcornerOrder (by rwa [hrightCorner])
      (by simpa only [hleftCorner, hrightCorner] using hqArc)
      ([] : List (RelLetter G Λ))
    have hvp : vertex B.secondBase B.secondArc p =
        vertex (vertex P.basepoint P.word B.secondVertex)
          (rotWord P.word B.secondVertex) p := by
      simpa only [secondBase, secondArc, secondHalf, List.append_nil,
        hleftCorner, hrightCorner] using hvpRot
    have hvq : vertex B.secondBase B.secondArc q =
        vertex (vertex P.basepoint P.word B.secondVertex)
          (rotWord P.word B.secondVertex) q := by
      simpa only [secondBase, secondArc, secondHalf, List.append_nil,
        hleftCorner, hrightCorner] using hvqRot
    by_cases htail : s < n - B.secondSide
    · have hsource : B.secondArcSource s = B.secondSide + s := by
        simp [secondArcSource, htail]
      have hsourceLt : B.secondArcSource s < n := by
        rw [hsource]
        omega
      have hleft : P.cut (B.secondArcSource s) ≤
          B.secondVertex + p := by
        by_cases hs0 : s = 0
        · subst s
          simp only [secondArcSource, if_pos (show 0 < n - B.secondSide by
            omega), Nat.add_zero]
          have hvertex := B.secondVertex_mem.1
          omega
        · have hcut := B.secondArcCut_of_pos_le_tail hs0 (by omega)
          rw [hcut] at hp
          have hvertex := B.secondVertex_mem.2.trans
            (P.polygonCut.mono_le (show B.secondSide + 1 ≤
              B.secondArcSource s by rw [hsource]; omega))
          omega
      have hright : B.secondVertex + q ≤
          P.cut (B.secondArcSource s + 1) := by
        have hcut := B.secondArcCut_of_pos_le_tail (s := s + 1)
          (by omega) (by omega)
        rw [hcut] at hq
        rw [show B.secondSide + (s + 1) =
          B.secondSide + s + 1 by omega] at hq
        rw [hsource]
        have hvertex := B.secondVertex_mem.2.trans
          (P.polygonCut.mono_le (show B.secondSide + 1 ≤
            B.secondSide + s + 1 by omega))
        omega
      have hqSuffix : q ≤ P.word.length - B.secondVertex := by
        have hcutLen := P.polygonCut.le_length
          (show B.secondArcSource s + 1 ≤ n by omega)
        omega
      have hpSuffix : p ≤ P.word.length - B.secondVertex :=
        hpq.trans hqSuffix
      have hvpOriginal := vertex_rotWord_le P.basepoint P.word hsecondLe p
        hpSuffix
      have hvqOriginal := vertex_rotWord_le P.basepoint P.word hsecondLe q
        hqSuffix
      have hparentQuasi := P.quasi (B.secondArcSource s) hsourceLt hparent
        (B.secondVertex + p) (B.secondVertex + q) hleft
        (Nat.add_le_add_left hpq _) hright
      have hdiff : B.secondVertex + q - (B.secondVertex + p) = q - p := by
        omega
      simpa only [hvp, hvq, hvpOriginal, hvqOriginal, hdiff] using
        hparentQuasi
    · have hsource : B.secondArcSource s =
          s - (n - B.secondSide) := by
        simp [secondArcSource, htail]
      have hsourceLe : B.secondArcSource s ≤ B.firstSide := by
        rw [hsource]
        omega
      have hsourceLt : B.secondArcSource s < n := by omega
      have hsEq : s =
          (n - B.secondSide) + B.secondArcSource s := by
        rw [hsource]
        omega
      have hcutStart := B.secondArcCut_tail_add hsourceLe
      rw [← hsEq] at hcutStart
      rw [hcutStart] at hp
      let suffix := P.word.length - B.secondVertex
      have hpAfter : suffix ≤ p := by dsimp [suffix]; omega
      have hqAfter : suffix ≤ q := hpAfter.trans hpq
      have hleft : P.cut (B.secondArcSource s) ≤ p - suffix := by
        dsimp [suffix]
        omega
      have hright : q - suffix ≤ P.cut (B.secondArcSource s + 1) := by
        by_cases hlast : B.secondArcSource s = B.firstSide
        · have hsLast : s =
              (n - B.secondSide) + B.firstSide := by omega
          rw [hsLast, B.secondArcCut_finish] at hq
          have hvertex := B.firstVertex_mem.2
          dsimp [suffix]
          omega
        · have hnextLe : B.secondArcSource s + 1 ≤ B.firstSide := by omega
          have hsNext : s + 1 =
              (n - B.secondSide) + (B.secondArcSource s + 1) := by omega
          have hcutFinish := B.secondArcCut_tail_add hnextLe
          rw [← hsNext] at hcutFinish
          rw [hcutFinish] at hq
          dsimp [suffix]
          omega
      have hpPrefix : p - suffix ≤ B.secondVertex := by
        have hfirstSecond := B.split_vertices_ordered
        dsimp [suffix]
        omega
      have hqPrefix : q - suffix ≤ B.secondVertex := by
        have hfirstSecond := B.split_vertices_ordered
        dsimp [suffix]
        omega
      have hvpOriginal := vertex_rotWord_add P.basepoint P.word hsecondLe
        P.closed p (p - suffix) (by dsimp [suffix]; omega) hpPrefix
      have hvqOriginal := vertex_rotWord_add P.basepoint P.word hsecondLe
        P.closed q (q - suffix) (by dsimp [suffix]; omega) hqPrefix
      have hparentQuasi := P.quasi (B.secondArcSource s) hsourceLt hparent
        (p - suffix) (q - suffix) hleft (by omega) hright
      have hdiff : q - suffix - (p - suffix) = q - p := by omega
      simpa only [hvp, hvq, hvpOriginal, hvqOriginal, hdiff] using
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
