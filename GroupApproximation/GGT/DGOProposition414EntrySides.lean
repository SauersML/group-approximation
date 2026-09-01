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

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
