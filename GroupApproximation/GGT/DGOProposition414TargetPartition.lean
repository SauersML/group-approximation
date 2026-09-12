import GroupApproximation.GGT.DGOProposition414PlacementProducer

/-!
# Canonical target partition for a balanced split

Every distinguished side consists of one edge.  Relative to the ordered split
vertices, that edge therefore lies either in the closed first arc or in the
wrapped complementary arc.  This file defines the two target filters and their
correct local coordinates, including the seam in the wrapped second arc.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace BalancedSplitData

def targetInFirstArc
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : Prop :=
  B.firstVertex ≤ P.cut s ∧ P.cut (s + 1) ≤ B.secondVertex

noncomputable def firstTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Finset ℕ := by
  classical
  exact P.target.filter B.targetInFirstArc

noncomputable def secondTarget
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) : Finset ℕ := by
  classical
  exact P.target.filter fun s => ¬ B.targetInFirstArc s

def firstTargetPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : ℕ :=
  P.cut s - B.firstVertex

/-- Wrapped coordinate based at the second split vertex.  Sources after the
vertex lie in the initial `drop`; sources before it lie after the seam. -/
def secondTargetPos
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) (s : ℕ) : ℕ :=
  if B.secondVertex ≤ P.cut s then P.cut s - B.secondVertex
  else P.word.length - B.secondVertex + P.cut s

theorem target_partition
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    Disjoint B.firstTarget B.secondTarget ∧
      P.target = B.firstTarget ∪ B.secondTarget := by
  classical
  constructor
  · rw [Finset.disjoint_left]
    intro s hs ht
    have hs' := Finset.mem_filter.mp hs
    have ht' := Finset.mem_filter.mp ht
    exact ht'.2 hs'.2
  · ext s
    by_cases h : B.targetInFirstArc s <;> simp [firstTarget, secondTarget, h]

theorem target_cut_injective
    {D : RelGenSet G Λ} {b : ℝ} {n : ℕ}
    (P : SumBoundInput D b n) : Set.InjOn P.cut (↑P.target : Set ℕ) := by
  intro s hs t ht heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hmono := P.polygonCut.mono_le (show s + 1 ≤ t by omega)
    rw [P.target_edge s hs, heq] at hmono
    omega
  · have hmono := P.polygonCut.mono_le (show t + 1 ≤ s by omega)
    rw [P.target_edge t ht, heq] at hmono
    omega

private theorem target_start_lt_wordLength
    {D : RelGenSet G Λ} {b : ℝ} {n s : ℕ}
    {P : SumBoundInput D b n} (hs : s ∈ P.target) :
    P.cut s < P.word.length := by
  have hcomp := P.target_component s hs
  exact hcomp.1.trans_le hcomp.2.1

theorem split_vertices_ordered
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.firstVertex ≤ B.secondVertex :=
  B.firstVertex_mem.2.trans
    ((P.polygonCut.mono_le (Nat.succ_le_iff.mpr B.side_order)).trans
      B.secondVertex_mem.1)

theorem firstTargetPos_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    Set.InjOn B.firstTargetPos (↑B.firstTarget : Set ℕ) := by
  classical
  intro s hs t ht heq
  have hs' := Finset.mem_filter.mp hs
  have ht' := Finset.mem_filter.mp ht
  unfold targetInFirstArc at hs' ht'
  apply target_cut_injective P hs'.1 ht'.1
  simp only [firstTargetPos] at heq
  omega

theorem outside_firstArc_cases
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    P.cut (s + 1) ≤ B.firstVertex ∨ B.secondVertex ≤ P.cut s := by
  classical
  have hs' := Finset.mem_filter.mp hs
  have hedge := P.target_edge s hs'.1
  have hout := hs'.2
  unfold targetInFirstArc at hout
  have horder := B.split_vertices_ordered
  omega

theorem firstTargetPos_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    B.firstTargetPos s < B.firstArcLength := by
  classical
  have hs' := Finset.mem_filter.mp hs
  have hedge := P.target_edge s hs'.1
  unfold targetInFirstArc at hs'
  simp only [firstTargetPos, firstArcLength]
  omega

theorem secondTargetPos_lt
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    B.secondTargetPos s < B.secondArcLength := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hslt := target_start_lt_wordLength hsTarget
  have hedge := P.target_edge s hsTarget
  have hcases := B.outside_firstArc_cases hs
  have hsecondLe : B.secondVertex ≤ P.word.length :=
    B.secondVertex_mem.2.trans
      (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))
  simp only [secondTargetPos, secondArcLength]
  split_ifs with hafter
  · omega
  · rcases hcases with hbefore | hafter'
    · omega
    · exact (hafter hafter').elim

theorem secondTargetPos_injective
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    Set.InjOn B.secondTargetPos (↑B.secondTarget : Set ℕ) := by
  intro s hs t ht heq
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have htTarget := (Finset.mem_filter.mp ht).1
  have hslt := target_start_lt_wordLength hsTarget
  have htlt := target_start_lt_wordLength htTarget
  apply target_cut_injective P hsTarget htTarget
  simp only [secondTargetPos] at heq
  by_cases hsAfter : B.secondVertex ≤ P.cut s
  · by_cases htAfter : B.secondVertex ≤ P.cut t
    · simp [hsAfter, htAfter] at heq
      omega
    · simp [hsAfter, htAfter] at heq
      omega
  · by_cases htAfter : B.secondVertex ≤ P.cut t
    · simp [hsAfter, htAfter] at heq
      omega
    · simp [hsAfter, htAfter] at heq
      omega

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
