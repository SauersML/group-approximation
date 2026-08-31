import GroupApproximation.GGT.DGOProposition414TargetPartition

/-!
# Transporting the canonical target partition into the balanced halves

This file supplies the component, isolation, and component-start fields left
open by `DGOProposition414TargetPartition`.  The wrapped second arc is handled
in the rotated original word, with the basepoint and terminal rotation cases
separated explicitly.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

private theorem isCompStart_firstHalf_arc_of_isComp
    (lam : Λ) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a d p : ℕ} (hd : c d ≤ w.length) (t : List (RelLetter G Λ))
    (hp : p < c d - c a)
    (hcomp : IsComp lam w (c a + p) (c a + p + 1)) :
    IsCompStart lam (firstHalf w c a d t) p := by
  have hplen : p < (firstHalf w c a d t).length := by
    rw [length_firstHalf w c hd]
    omega
  have hwlen : c a + p < w.length := by omega
  have hcoW : (w[c a + p]'hwlen).IsCompOf lam :=
    hcomp.2.2.1 _ le_rfl hcomp.1 hwlen
  have hcoHalf : ((firstHalf w c a d t)[p]'hplen).IsCompOf lam :=
    (isCompOf_firstHalf_arc_iff lam w c hd hp t hplen).mpr hcoW
  obtain ⟨q, r, hqp, hpr, hqr⟩ :=
    exists_isComp_of_isCompOf lam (firstHalf w c a d t) p hplen hcoHalf
  have hq : q = p := by
    by_contra hne
    have hqp' : q < p := by omega
    have hp0 : 0 < p := by omega
    have hprevLen : p - 1 < (firstHalf w c a d t).length := by omega
    have hprevHalf :
        ((firstHalf w c a d t)[p - 1]'hprevLen).IsCompOf lam :=
      hqr.2.2.1 (p - 1) (by omega) (by omega) hprevLen
    have hpPrevArc : p - 1 < c d - c a := by omega
    have hprevW : (w[c a + (p - 1)]'(by omega)).IsCompOf lam :=
      (isCompOf_firstHalf_arc_iff lam w c hd hpPrevArc t hprevLen).mp
        hprevHalf
    exact hcomp.2.2.2.1 (c a + (p - 1)) (by omega) (by omega) hprevW
  exact ⟨r, by rw [← hq]; exact hqr⟩

omit [Group G] in
private theorem isCompStart_secondHalf_arc_of_isComp
    (lam : Λ) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a d p : ℕ} (ha : c a ≤ c d) (hd : c d ≤ w.length)
    (t : List (RelLetter G Λ))
    (hp : p < (w.length - c d) + c a)
    (hcomp : IsComp lam (rotWord w (c d)) p (p + 1)) :
    IsCompStart lam (secondHalf w c a d t) p := by
  have hplen : p < (secondHalf w c a d t).length := by
    rw [length_secondHalf w c (ha.trans hd)]
    omega
  have hrotlen : p < (rotWord w (c d)).length := by
    rw [length_rotWord w hd]
    have := hcomp.2.1
    omega
  have hcoRot : ((rotWord w (c d))[p]'hrotlen).IsCompOf lam :=
    hcomp.2.2.1 _ le_rfl hcomp.1 hrotlen
  have hcoHalf : ((secondHalf w c a d t)[p]'hplen).IsCompOf lam :=
    (isCompOf_secondHalf_rotWord_iff lam w c ha hd hp t hplen).mpr hcoRot
  obtain ⟨q, r, hqp, hpr, hqr⟩ :=
    exists_isComp_of_isCompOf lam (secondHalf w c a d t) p hplen hcoHalf
  have hq : q = p := by
    by_contra hne
    have hqp' : q < p := by omega
    have hp0 : 0 < p := by omega
    have hprevLen : p - 1 < (secondHalf w c a d t).length := by omega
    have hprevHalf :
        ((secondHalf w c a d t)[p - 1]'hprevLen).IsCompOf lam :=
      hqr.2.2.1 (p - 1) (by omega) (by omega) hprevLen
    have hpPrevArc : p - 1 < (w.length - c d) + c a := by omega
    have hprevRot :
        ((rotWord w (c d))[p - 1]'(by rw [length_rotWord w hd]; omega)).IsCompOf lam :=
      (isCompOf_secondHalf_rotWord_iff lam w c ha hd hpPrevArc t
        hprevLen).mp hprevHalf
    exact hcomp.2.2.2.1 (p - 1) (by omega) (by omega) hprevRot
  exact ⟨r, by rw [← hq]; exact hqr⟩

namespace BalancedSplitData

private theorem secondVertex_le_length
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    B.secondVertex ≤ P.word.length :=
  B.secondVertex_mem.2.trans
    (P.polygonCut.le_length (Nat.succ_le_iff.mpr B.secondSide_lt))

theorem first_original_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    IsComp (P.label s) P.word
      (B.firstVertex + B.firstTargetPos s)
      (B.firstVertex + B.firstTargetPos s + 1) := by
  classical
  have hs' := Finset.mem_filter.mp hs
  unfold targetInFirstArc at hs'
  have hedge := P.target_edge s hs'.1
  have hpos : B.firstVertex + B.firstTargetPos s = P.cut s := by
    simp only [firstTargetPos]
    omega
  rw [hpos, ← hedge]
  exact P.target_component s hs'.1

theorem first_original_isolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    IsIsolated D.fam (P.label s) P.basepoint P.word
      (B.firstVertex + B.firstTargetPos s) := by
  classical
  have hs' := Finset.mem_filter.mp hs
  unfold targetInFirstArc at hs'
  have hpos : B.firstVertex + B.firstTargetPos s = P.cut s := by
    simp only [firstTargetPos]
    omega
  rw [hpos]
  exact P.target_isolated s hs'.1

theorem second_rotated_component
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    IsComp (P.label s) (rotWord P.word B.secondVertex)
      (B.secondTargetPos s) (B.secondTargetPos s + 1) := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hedge := P.target_edge s hsTarget
  have hcomp : IsComp (P.label s) P.word (P.cut s) (P.cut s + 1) := by
    rw [← hedge]
    exact P.target_component s hsTarget
  have hJle := B.secondVertex_le_length
  by_cases hafter : B.secondVertex ≤ P.cut s
  · by_cases hs0 : P.cut s = 0
    · have hJ0 : B.secondVertex = 0 := by omega
      simpa [secondTargetPos, hafter, hs0, hJ0, rotWord] using hcomp
    · have hwrap := notMem_wrap_of_isIsolated D (P.label s) P.basepoint
        P.letters P.closed hcomp (P.target_isolated s hsTarget) (by omega)
      have hrot := isComp_rotWord_of_le (P.label s) hcomp hafter hJle hwrap
      have hend : P.cut s + 1 - B.secondVertex =
          P.cut s - B.secondVertex + 1 := by omega
      rw [hend] at hrot
      simpa [secondTargetPos, hafter] using hrot
  · have hbefore := (B.outside_firstArc_cases hs).resolve_right hafter
    rw [hedge] at hbefore
    have hbeforeJ : P.cut s + 1 ≤ B.secondVertex :=
      hbefore.trans B.split_vertices_ordered
    by_cases hJend : B.secondVertex = P.word.length
    · have hrot : rotWord P.word B.secondVertex = P.word := by
        simp [hJend, rotWord]
      have hpos : B.secondTargetPos s = P.cut s := by
        rw [secondTargetPos, if_neg hafter, hJend, Nat.sub_self,
          Nat.zero_add]
      simpa [hrot, hpos] using hcomp
    · have hJlt : B.secondVertex < P.word.length := lt_of_le_of_ne hJle hJend
      by_cases hs0 : P.cut s = 0
      · rw [hs0] at hcomp
        have hiso0 := P.target_isolated s hsTarget
        rw [hs0] at hiso0
        have hbefore0 : 0 + 1 ≤ B.secondVertex := by omega
        have hrot := isComp_rotWord_zero_before (P.label s) hJlt hcomp
          hbefore0
          (notMem_terminal_of_isIsolated_zero D (P.label s) P.basepoint
            P.letters P.closed hcomp hiso0 (by omega))
        have hJpos : 0 < B.secondVertex := by omega
        simpa [secondTargetPos, hafter, hs0, hJpos.ne'] using hrot
      · have hrot := isComp_rotWord_before (P.label s) hJle hcomp hbeforeJ
          (by omega)
        have hend : P.word.length - B.secondVertex + (P.cut s + 1) =
            P.word.length - B.secondVertex + P.cut s + 1 := by omega
        rw [hend] at hrot
        simpa [secondTargetPos, hafter] using hrot

theorem second_rotated_isolated
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    IsIsolated D.fam (P.label s) B.secondBase
      (rotWord P.word B.secondVertex) (B.secondTargetPos s) := by
  classical
  have hsTarget := (Finset.mem_filter.mp hs).1
  have hedge := P.target_edge s hsTarget
  have hcomp : IsComp (P.label s) P.word (P.cut s) (P.cut s + 1) := by
    rw [← hedge]
    exact P.target_component s hsTarget
  have hiso := P.target_isolated s hsTarget
  have hJle := B.secondVertex_le_length
  by_cases hafter : B.secondVertex ≤ P.cut s
  · by_cases hs0 : P.cut s = 0
    · have hJ0 : B.secondVertex = 0 := by omega
      simpa [BalancedSplitData.secondBase, secondTargetPos, hafter, hs0,
        hJ0, rotWord] using hiso
    · have hwrap := notMem_wrap_of_isIsolated D (P.label s) P.basepoint
        P.letters P.closed hcomp hiso (by omega)
      have hrot := isIsolated_rotWord_of_le D (P.label s) P.basepoint
        P.letters P.closed hcomp hiso hafter hJle hwrap
      simpa [BalancedSplitData.secondBase, secondTargetPos, hafter] using hrot
  · have hbefore := (B.outside_firstArc_cases hs).resolve_right hafter
    rw [hedge] at hbefore
    have hbeforeJ : P.cut s + 1 ≤ B.secondVertex :=
      hbefore.trans B.split_vertices_ordered
    by_cases hJend : B.secondVertex = P.word.length
    · have hvertex : vertex P.basepoint P.word B.secondVertex = P.basepoint := by
        rw [hJend, vertex_length_of_closed P.basepoint P.word P.closed]
      have hrot : rotWord P.word B.secondVertex = P.word := by
        simp [hJend, rotWord]
      have hpos : B.secondTargetPos s = P.cut s := by
        rw [secondTargetPos, if_neg hafter, hJend, Nat.sub_self,
          Nat.zero_add]
      simpa [BalancedSplitData.secondBase, hvertex, hrot, hpos] using hiso
    · have hJlt : B.secondVertex < P.word.length := lt_of_le_of_ne hJle hJend
      by_cases hs0 : P.cut s = 0
      · rw [hs0] at hcomp hiso
        have hbefore0 : 0 + 1 ≤ B.secondVertex := by omega
        have hrot := isIsolated_rotWord_zero_before D (P.label s) P.basepoint
          P.letters P.closed hJlt hcomp hbefore0 hiso
        have hJpos : 0 < B.secondVertex := by omega
        simpa [BalancedSplitData.secondBase, secondTargetPos, hafter, hs0,
          hJpos.ne'] using hrot
      · have hrot := isIsolated_rotWord_before D (P.label s) P.basepoint
          P.letters P.closed hJlt hcomp hbeforeJ (by omega) hiso
        simpa [BalancedSplitData.secondBase, secondTargetPos, hafter] using hrot

theorem first_target_start
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.firstTarget) :
    IsCompStart (P.label s) B.firstWord (B.firstTargetPos s) := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_le_length
  have hcomp := B.first_original_component hs
  rw [← hleft] at hcomp
  apply isCompStart_firstHalf_arc_of_isComp (P.label s) P.word B.refinedCut
    hEnd B.chord
  · simpa only [hleft, hright, firstArcLength] using B.firstTargetPos_lt hs
  · simpa only [BalancedSplitData.firstWord] using hcomp

theorem second_target_start
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R s : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R)
    (hs : s ∈ B.secondTarget) :
    IsCompStart (P.label s) B.secondWord (B.secondTargetPos s) := by
  have hleft : B.refinedCut (B.firstSide + 1) = B.firstVertex := by
    simp [refinedCut, splitPairCut_left B.side_order]
  have hright : B.refinedCut (B.secondSide + 2) = B.secondVertex := by
    simp [refinedCut, splitPairCut_right]
  have hEnd : B.refinedCut (B.secondSide + 2) ≤ P.word.length := by
    rw [hright]
    exact B.secondVertex_le_length
  have hStartEnd : B.refinedCut (B.firstSide + 1) ≤
      B.refinedCut (B.secondSide + 2) := by
    rw [hleft, hright]
    exact B.split_vertices_ordered
  apply isCompStart_secondHalf_arc_of_isComp (P.label s) P.word B.refinedCut
    hStartEnd hEnd B.chord
  · simpa only [hleft, hright, secondArcLength] using B.secondTargetPos_lt hs
  · have hcomp := B.second_rotated_component hs
    rw [← hright] at hcomp
    simpa only [BalancedSplitData.secondWord] using hcomp

/-- The canonical target partition and its transported components instantiate
the exact arc-placement input with no additional geometric premise. -/
noncomputable def arcPlacement
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    BalancedSplitArcPlacement D hsymm b hδ P B where
  firstTarget := B.firstTarget
  secondTarget := B.secondTarget
  target_disjoint := B.target_partition.1
  target_cover := B.target_partition.2
  firstPos := B.firstTargetPos
  secondPos := B.secondTargetPos
  firstPos_injective := B.firstTargetPos_injective
  secondPos_injective := B.secondTargetPos_injective
  first_pos_lt := fun _s hs => B.firstTargetPos_lt hs
  second_pos_lt := fun _s hs => B.secondTargetPos_lt hs
  first_start := fun _s hs => B.first_target_start hs
  second_start := fun _s hs => B.second_target_start hs
  first_original_component := fun _s hs => B.first_original_component hs
  first_original_isolated := fun _s hs => B.first_original_isolated hs
  second_rotated_component := fun _s hs => B.second_rotated_component hs
  second_rotated_isolated := fun _s hs => B.second_rotated_isolated hs

/-- The raw balanced split now has its full component placement, with
separation and chord partners supplied by `PlacementProducer`. -/
noncomputable def componentPlacement
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    BalancedSplitComponentPlacement D hsymm b hδ P B :=
  BalancedSplitArcPlacement.componentPlacement B.arcPlacement

/-- The canonical target transport therefore produces both greedy broken-half
assignments without any extra placement premise. -/
noncomputable def brokenAssignment
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    TwoHalfBrokenAssignment B.componentPlacement.firstTarget
      B.componentPlacement.secondTarget
      B.componentPlacement.firstSurvives B.componentPlacement.secondSurvives
      B.componentPlacement.firstPos B.componentPlacement.secondPos
      B.chord.length :=
  Classical.choice B.componentPlacement.exists_twoHalfBrokenAssignment

end BalancedSplitData

end DGOProposition414
end GGT
end GroupApproximation
