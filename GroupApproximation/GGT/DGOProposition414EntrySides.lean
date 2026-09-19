import GroupApproximation.GGT.DGOProposition414PartnerEndpoints

/-!
# Canonical side coordinates of balanced-half targets

The greedy enumeration is ordered by word positions, while inherited subarcs
are cut at polygon-side coordinates.  This file identifies the exact side of
each transported target in both balanced arcs.  The two inserted split points
are handled at the boundary sides, where target containment forces the
relevant original cut vertex to equal the inserted point.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

/-- Side coordinate of a target in the ordinary first inherited arc. -/
def firstTargetSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : ℕ :=
  s - B.firstSide

/-- Side coordinate of a target in the wrapped complementary arc. -/
def secondTargetSide
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : ℕ :=
  if B.secondSide ≤ s then s - B.secondSide else n - B.secondSide + s

private theorem firstTarget_side_bounds
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.firstTarget) :
    B.firstSide ≤ s ∧ s ≤ B.secondSide := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hcontain := (Finset.mem_filter.mp hs).2
  change B.firstVertex ≤ P.cut s ∧ P.cut (s + 1) ≤ B.secondVertex at hcontain
  have hslt : s < n := P.target_lt s hsTarget
  constructor
  · by_contra h
    have hmono := P.polygonCut.mono_le (show s + 1 ≤ B.firstSide by omega)
    have hcut := B.firstVertex_mem.1
    have hedge := P.target_edge s hsTarget
    rw [hedge] at hmono
    omega
  · by_contra h
    have hmono := P.polygonCut.mono_le
      (show B.secondSide + 1 ≤ s by omega)
    have hcut := B.secondVertex_mem.2
    have hedge := P.target_edge s hsTarget
    rw [hedge] at hcontain
    omega

private theorem refinedCut_firstTarget_start
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.firstTarget) :
    B.refinedCut (B.firstSide + 1 + B.firstTargetSide s) = P.cut s := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hcontain := (Finset.mem_filter.mp hs).2
  have hb := (B.firstTarget_side_bounds hs).1
  have ht := (B.firstTarget_side_bounds hs).2
  by_cases hsa : s = B.firstSide
  · subst s
    have heq : P.cut B.firstSide = B.firstVertex := by
      have := B.firstVertex_mem.1
      exact le_antisymm this hcontain.1
    simp [firstTargetSide, refinedCut, splitPairCut_left B.side_order, heq]
  · have hsa' : B.firstSide < s := by omega
    have hindex : B.firstSide + 1 + B.firstTargetSide s = s + 1 := by
      simp [firstTargetSide]
      omega
    rw [hindex]
    unfold refinedCut splitPairCut insertPointCut
    simp only [if_pos (show s + 1 ≤ B.secondSide + 1 by omega),
      if_neg (show ¬s + 1 ≤ B.firstSide by omega),
      if_neg (show s + 1 ≠ B.firstSide + 1 by omega)]
    congr 1

private theorem refinedCut_firstTarget_finish
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.firstTarget) :
    B.refinedCut (B.firstSide + 1 + (B.firstTargetSide s + 1)) =
      P.cut (s + 1) := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hcontain := (Finset.mem_filter.mp hs).2
  have hb := (B.firstTarget_side_bounds hs).1
  have ht := (B.firstTarget_side_bounds hs).2
  have hindex : B.firstSide + 1 + (B.firstTargetSide s + 1) = s + 2 := by
    simp [firstTargetSide]
    omega
  rw [hindex]
  by_cases hsb : s = B.secondSide
  · subst s
    have heq : P.cut (B.secondSide + 1) = B.secondVertex := by
      exact le_antisymm hcontain.2 B.secondVertex_mem.2
    simp [refinedCut, splitPairCut_right, heq]
  · have hsb' : s < B.secondSide := by omega
    unfold refinedCut splitPairCut insertPointCut
    simp only [if_pos (show s + 2 ≤ B.secondSide + 1 by omega),
      if_neg (show ¬s + 2 ≤ B.firstSide by omega),
      if_neg (show s + 2 ≠ B.firstSide + 1 by omega)]
    congr 1

/-- A first-half target occupies exactly its named inherited-arc side. -/
theorem firstArcCut_target
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.firstTarget) :
    B.firstArcCut (B.firstTargetSide s) = B.firstTargetPos s ∧
      B.firstArcCut (B.firstTargetSide s + 1) = B.firstTargetPos s + 1 := by
  classical
  have hbase : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hedge := P.target_edge s (Finset.mem_filter.mp hs).1
  constructor
  · simp only [firstArcCut, firstTargetPos]
    rw [B.refinedCut_firstTarget_start hs, hbase]
  · simp only [firstArcCut, firstTargetPos]
    rw [B.refinedCut_firstTarget_finish hs, hbase, hedge]
    have hle := (Finset.mem_filter.mp hs).2.1
    omega

/-- Every first-half target side lies strictly inside the inherited side
range. -/
theorem firstTargetSide_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.firstTarget) :
    B.firstTargetSide s < B.secondSide - B.firstSide + 1 := by
  have hb := (B.firstTarget_side_bounds hs).1
  have ht := (B.firstTarget_side_bounds hs).2
  simp [firstTargetSide]
  omega

private theorem refinedPolygonCut_for_entrySides
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    IsPolygonCut (n + 2) P.word B.refinedCut :=
  isPolygonCut_splitPair P.polygonCut B.side_order B.secondSide_lt
    B.firstVertex_mem.1 B.firstVertex_mem.2 B.secondVertex_mem.1
    B.secondVertex_mem.2

private theorem refinedCut_before_first
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ≤ B.firstSide) :
    B.refinedCut s = P.cut s := by
  have horder := B.side_order
  unfold refinedCut splitPairCut insertPointCut
  rw [if_pos (show s ≤ B.secondSide + 1 by omega), if_pos hs]

private theorem refinedCut_after_second
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : B.secondSide < s) :
    B.refinedCut (s + 2) = P.cut s := by
  have horder := B.side_order
  unfold refinedCut splitPairCut insertPointCut
  rw [if_neg (show ¬s + 2 ≤ B.secondSide + 1 by omega),
    if_neg (show s + 2 ≠ B.secondSide + 2 by omega),
    if_neg (show ¬s + 2 - 1 ≤ B.firstSide by omega),
    if_neg (show s + 2 - 1 ≠ B.firstSide + 1 by omega)]
  congr 1

private theorem secondTarget_after_iff
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.secondTarget) :
    B.secondSide ≤ s ↔ B.secondVertex ≤ P.cut s := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hedge := P.target_edge s hsTarget
  have horder := B.side_order
  constructor
  · intro hside
    rcases B.outside_firstArc_cases hs with hbefore | hafter
    · have hmono := P.polygonCut.mono_le
        (show B.firstSide + 1 ≤ s by omega)
      have hfirst := B.firstVertex_mem.2
      rw [hedge] at hbefore
      omega
    · exact hafter
  · intro hafter
    by_contra hside
    have hmono := P.polygonCut.mono_le
      (show s + 1 ≤ B.secondSide by omega)
    have hsecond := B.secondVertex_mem.1
    rw [hedge] at hmono
    omega

private theorem secondTarget_before_of_not_after
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.secondTarget)
    (hside : ¬ B.secondSide ≤ s) :
    s ≤ B.firstSide ∧ P.cut (s + 1) ≤ B.firstVertex := by
  classical
  have hafter : ¬ B.secondVertex ≤ P.cut s := by
    exact fun h => hside ((B.secondTarget_after_iff hs).mpr h)
  have hbefore := (B.outside_firstArc_cases hs).resolve_right hafter
  have hsTarget := (Finset.mem_filter.mp hs).1
  by_contra hnot
  have hmono := P.polygonCut.mono_le
    (show B.firstSide + 1 ≤ s by omega)
  have hfirst := B.firstVertex_mem.2
  have hedge := P.target_edge s hsTarget
  rw [hedge] at hbefore
  omega

private theorem secondArcCut_after
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.secondTarget)
    (hside : B.secondSide ≤ s) :
    B.secondArcCut (s - B.secondSide) = P.cut s - B.secondVertex ∧
      B.secondArcCut (s - B.secondSide + 1) =
        P.cut (s + 1) - B.secondVertex := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hslt := P.target_lt s hsTarget
  have hafter := (B.secondTarget_after_iff hs).mp hside
  have hbase : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have houterStart : s - B.secondSide ≤
      (n + 2 - (B.secondSide + 2)) + (B.firstSide + 1) := by omega
  have houterFinish : s - B.secondSide + 1 ≤
      (n + 2 - (B.secondSide + 2)) + (B.firstSide + 1) := by omega
  have hinnerStart : s - B.secondSide ≤ n + 2 - (B.secondSide + 2) := by omega
  have hinnerFinish : s - B.secondSide + 1 ≤ n + 2 - (B.secondSide + 2) := by omega
  simp only [secondArcCut,
    appendCut_apply_of_le _ _ _ _ houterStart,
    appendCut_apply_of_le _ _ _ _ houterFinish,
    appendCut_apply_of_le _ _ _ _ hinnerStart,
    appendCut_apply_of_le _ _ _ _ hinnerFinish]
  constructor
  · by_cases heq : s = B.secondSide
    · subst s
      have hcut : P.cut B.secondSide = B.secondVertex :=
        le_antisymm B.secondVertex_mem.1 hafter
      simp [hbase, hcut]
    · have hgt : B.secondSide < s := by omega
      rw [show B.secondSide + 2 + (s - B.secondSide) = s + 2 by omega,
        B.refinedCut_after_second hgt, hbase]
  · rw [show B.secondSide + 2 + (s - B.secondSide + 1) = (s + 1) + 2 by omega,
      B.refinedCut_after_second (show B.secondSide < s + 1 by omega), hbase]

private theorem secondArcCut_before
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.secondTarget)
    (hside : ¬ B.secondSide ≤ s) :
    B.secondArcCut (n - B.secondSide + s) =
        P.word.length - B.secondVertex + P.cut s ∧
      B.secondArcCut (n - B.secondSide + s + 1) =
        P.word.length - B.secondVertex + P.cut (s + 1) := by
  classical
  let tail := n + 2 - (B.secondSide + 2)
  have htail : tail = n - B.secondSide := by dsimp [tail]; omega
  have hbefore := B.secondTarget_before_of_not_after hs hside
  have hsecond := B.secondSide_lt
  have houterStart : tail + s ≤ tail + (B.firstSide + 1) := by omega
  have houterFinish : tail + s + 1 ≤ tail + (B.firstSide + 1) := by omega
  have hzero : B.refinedCut 0 = 0 := B.refinedPolygonCut_for_entrySides.start
  have hinnerStart := appendCut_apply_add
    (fun r => B.refinedCut (B.secondSide + 2 + r) -
      B.refinedCut (B.secondSide + 2)) B.refinedCut tail s hzero
  have hinnerFinish := appendCut_apply_add
    (fun r => B.refinedCut (B.secondSide + 2 + r) -
      B.refinedCut (B.secondSide + 2)) B.refinedCut tail (s + 1) hzero
  have hbase : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hend : B.refinedCut (B.secondSide + 2 + tail) = P.word.length := by
    have hidx : B.secondSide + 2 + tail = n + 2 := by dsimp [tail]; omega
    rw [hidx]
    exact B.refinedPolygonCut_for_entrySides.finish
  rw [← htail]
  change B.secondArcCut (tail + s) =
      P.word.length - B.secondVertex + P.cut s ∧
    B.secondArcCut (tail + s + 1) =
      P.word.length - B.secondVertex + P.cut (s + 1)
  rw [secondArcCut,
    appendCut_apply_of_le _ _ _ _ houterStart,
    appendCut_apply_of_le _ _ _ _ houterFinish,
    hinnerStart]
  rw [show tail + s + 1 = tail + (s + 1) by omega, hinnerFinish, hend, hbase]
  constructor
  · rw [B.refinedCut_before_first hbefore.1]
  · by_cases heq : s = B.firstSide
    · subst s
      have hcut : P.cut (B.firstSide + 1) = B.firstVertex :=
        le_antisymm hbefore.2 B.firstVertex_mem.2
      have href : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
        simp [refinedCut, splitPairCut_left B.side_order]
      rw [href, hcut]
    · rw [B.refinedCut_before_first (show s + 1 ≤ B.firstSide by omega)]

/-- A wrapped-half target occupies exactly its canonical inherited-arc side,
including both sides of the cyclic seam. -/
theorem secondArcCut_target
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.secondTarget) :
    B.secondArcCut (B.secondTargetSide s) = B.secondTargetPos s ∧
      B.secondArcCut (B.secondTargetSide s + 1) = B.secondTargetPos s + 1 := by
  classical
  have hedge := P.target_edge s (Finset.mem_filter.mp hs).1
  by_cases hside : B.secondSide ≤ s
  · have h := B.secondArcCut_after hs hside
    rw [hedge] at h
    have hafter := (B.secondTarget_after_iff hs).mp hside
    have hfinish : P.cut s + 1 - B.secondVertex =
        P.cut s - B.secondVertex + 1 := by omega
    rw [hfinish] at h
    simpa [secondTargetSide, secondTargetPos, hside,
      hafter] using h
  · have h := B.secondArcCut_before hs hside
    rw [hedge] at h
    have hafter : ¬ B.secondVertex ≤ P.cut s := by
      exact fun h' => hside ((B.secondTarget_after_iff hs).mpr h')
    simpa [secondTargetSide, secondTargetPos, hside, hafter,
      Nat.add_assoc] using h

/-- Every wrapped-half target side lies strictly inside the inherited side
range. -/
theorem secondTargetSide_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (hs : s ∈ B.secondTarget) :
    B.secondTargetSide s < (n - B.secondSide) + B.firstSide + 1 := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hslt := P.target_lt s hsTarget
  by_cases hside : B.secondSide ≤ s
  · simp [secondTargetSide, hside]
    omega
  · have hbefore := B.secondTarget_before_of_not_after hs hside
    simp [secondTargetSide, hside]
    omega

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
